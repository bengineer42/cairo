use std::collections::{HashMap, HashSet};
use std::num::NonZeroUsize;
use std::ops::Deref;
use std::panic::{catch_unwind, AssertUnwindSafe};

use anyhow::Result;
use cairo_lang_defs::db::DefsGroup;
use cairo_lang_filesystem::db::FilesGroup;
use cairo_lang_filesystem::ids::{FileId, FileLongId};
use cairo_lang_lowering::db::LoweringGroup;
use cairo_lang_lowering::diagnostic::LoweringDiagnostic;
use cairo_lang_parser::db::ParserGroup;
use cairo_lang_parser::ParserDiagnostic;
use cairo_lang_semantic::db::SemanticGroup;
use cairo_lang_semantic::SemanticDiagnostic;
use cairo_lang_utils::{LookupIntern, Upcast};
use crossbeam::channel::{Receiver, Sender, TryRecvError};
use lsp_types::notification::PublishDiagnostics;
use lsp_types::{PublishDiagnosticsParams, Url};
use salsa::ParallelDatabase;
use tracing::{error, trace_span, warn};

use crate::lang::db::AnalysisDatabase;
use crate::lang::diagnostics::lsp::map_cairo_diagnostics_to_lsp;
use crate::lang::lsp::LsProtoGroup;
use crate::server::client::Notifier;
use crate::server::schedule::thread;
use crate::server::schedule::thread::ThreadPriority;
use crate::state::{Snapshot, State};
use crate::{Backend, UnwindErrorKind};

const WORKERS_THREAD_POOL_SIZE: usize = 4;
const _: () = assert!(WORKERS_THREAD_POOL_SIZE != 0);

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FileDiagnostics {
    parser: cairo_lang_diagnostics::Diagnostics<ParserDiagnostic>,
    semantic: cairo_lang_diagnostics::Diagnostics<SemanticDiagnostic>,
    lowering: cairo_lang_diagnostics::Diagnostics<LoweringDiagnostic>,
}

impl FileDiagnostics {
    pub fn is_empty(&self) -> bool {
        self.semantic.is_empty() && self.lowering.is_empty() && self.parser.is_empty()
    }
}

#[derive(Debug, Default)]
struct DiagnosticsState {
    diagnostics_for_file: HashMap<Url, FileDiagnostics>,
}

#[derive(Debug)]
enum FileDiagnosticsChange {
    Replaced(FileDiagnostics),
    Unchanged,
    Unset,
}

pub struct StateSnapshotForDiagnostics {
    db_snapshots: [salsa::Snapshot<AnalysisDatabase>; WORKERS_THREAD_POOL_SIZE],
    open_files: Snapshot<HashSet<Url>>,
    trace_macro_diagnostics: bool,
}

impl StateSnapshotForDiagnostics {
    pub fn from_state(state: &mut State) -> Self {
        Self {
            db_snapshots: core::array::from_fn(|_| state.db.snapshot()),
            open_files: state.open_files.snapshot(),
            trace_macro_diagnostics: state.config.trace_macro_diagnostics,
        }
    }
}

pub struct Diagnostics {
    state: DiagnosticsState,
    notifier: Notifier,
    thread_pool: thread::Pool,
}

fn get_latest<T>(rx: &Receiver<T>) -> Option<T> {
    let mut last_msg = None;

    // Loop through all available messages, keeping only the last
    loop {
        match rx.try_recv() {
            Ok(msg) => {
                last_msg = Some(msg);
            }
            Err(TryRecvError::Disconnected) => return None,
            Err(TryRecvError::Empty) => {
                return match last_msg {
                    Some(msg) => Some(msg),
                    None => rx.recv().ok(),
                };
            }
        }
    }
}

impl Diagnostics {
    pub fn spawn() -> Result<(Sender<StateSnapshotForDiagnostics>, impl FnOnce(Notifier))> {
        let (sender, receiver) = crossbeam::channel::bounded(1);

        let handle = move |notifier| {
            let mut diagnostics = Self::new(notifier);

            while let Some(message) = get_latest(&receiver) {
                refresh_diagnostics(message, &mut diagnostics);
            }
        };

        Ok((sender, handle))
    }

    fn new(notifier: Notifier) -> Self {
        Self {
            state: Default::default(),
            thread_pool: thread::Pool::new(NonZeroUsize::new(WORKERS_THREAD_POOL_SIZE).unwrap()),
            notifier,
        }
    }
}

struct StateDiff {
    changes: HashMap<Url, FileDiagnosticsChange>,
    calculated_all: bool,
}

impl StateDiff {
    fn new() -> Self {
        Self { changes: Default::default(), calculated_all: true }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FileBothFormats {
    id: FileId,
    url: Url,
}

impl FileBothFormats {
    fn new(id: FileId, url: Url) -> Self {
        Self { id, url }
    }
}

/// Refresh diagnostics and send diffs to the client.
#[tracing::instrument(level = "debug", skip_all)]
pub fn refresh_diagnostics(message: StateSnapshotForDiagnostics, diagnostics: &mut Diagnostics) {
    let db = &message.db_snapshots[0]; // Safe because there is more than 0 workers

    let mut rest_of_files = HashSet::new();
    let Ok(open_files) = Backend::catch_cancellation(|| {
        let open_files = trace_span!("get_open_files_ids").in_scope(|| {
            message
                .open_files
                .owned()
                .into_iter()
                .filter_map(|url| db.file_for_url(&url).map(|file| FileBothFormats::new(file, url)))
                .collect::<Vec<_>>()
        });

        for crate_id in db.crates() {
            for module_id in db.crate_modules(crate_id).iter() {
                if let Ok(module_files) = db.module_files(*module_id) {
                    let unprocessed_files = module_files.iter().copied().filter(|file_id| {
                        matches!(file_id.lookup_intern(db.deref()), FileLongId::OnDisk(_))
                    });
                    rest_of_files.extend(
                        unprocessed_files
                            .map(|file| FileBothFormats::new(file, db.url_for_file(file))),
                    );
                }
            }
        }

        open_files
    }) else {
        // salsa failure while preparing state for workers.
        // Probably very fast cancellation, skip further work as it will fail anyway.
        return;
    };

    for file in &open_files {
        // remove open files from rest of files
        rest_of_files.remove(file);
    }

    let (sender, receiver) = crossbeam::channel::bounded(WORKERS_THREAD_POOL_SIZE);

    for (worker, db) in message.db_snapshots.into_iter().enumerate() {
        let trace_macro_diagnostics = message.trace_macro_diagnostics;
        let files =
            prepare_worker_state(open_files.iter().cloned(), rest_of_files.iter().cloned(), worker);

        let mut previous_file_diagnostics = HashMap::<Url, FileDiagnostics>::new();

        for (diags, url) in files.iter().filter_map(|file| {
            diagnostics
                .state
                .diagnostics_for_file
                .get(&file.url)
                .map(|diags| (diags.clone(), file.url.clone()))
        }) {
            previous_file_diagnostics.insert(url, diags);
        }

        spawn_worker_tasks(
            files,
            db,
            trace_macro_diagnostics,
            sender.clone(),
            previous_file_diagnostics,
            diagnostics,
        );
    }

    let mut state_diff = StateDiff::new();

    // for some reason rx is not disconnected after all thread completed
    for (partial_response, all) in receiver.into_iter().take(WORKERS_THREAD_POOL_SIZE) {
        state_diff.changes.extend(partial_response);

        if !all {
            state_diff.calculated_all = false;
        }
    }

    clear_old_diagnostics(diagnostics, state_diff);
}

#[tracing::instrument(skip_all)]
fn clear_old_diagnostics(diagnostics: &mut Diagnostics, mut state_diff: StateDiff) {
    diagnostics.state.diagnostics_for_file.retain(|url, old_diags| {
        match state_diff.changes.remove(url) {
            Some(FileDiagnosticsChange::Replaced(diags)) => {
                *old_diags = diags;

                true
            }
            Some(FileDiagnosticsChange::Unchanged) => true,
            Some(FileDiagnosticsChange::Unset) => false,
            None => {
                if state_diff.calculated_all {
                    // in case of empty state_diff this branch is always executed
                    clear(&diagnostics.notifier, url.clone());
                }

                !state_diff.calculated_all
            }
        }
    });

    // Files that were not previously tracked
    for (file, diags) in state_diff.changes {
        let FileDiagnosticsChange::Replaced(diags) = diags else {
            continue;
        };

        diagnostics.state.diagnostics_for_file.insert(file, diags);
    }
}

fn clear(notifier: &Notifier, file: Url) {
    trace_span!("publish_diagnostics").in_scope(|| {
        notifier.notify::<PublishDiagnostics>(PublishDiagnosticsParams {
            uri: file,
            diagnostics: vec![],
            version: None,
        })
    });
}

fn prepare_worker_state(
    open_files_ids: impl Iterator<Item = FileBothFormats>,
    rest_of_files: impl Iterator<Item = FileBothFormats>,
    worker: usize,
) -> Vec<FileBothFormats> {
    // Important: keep open files first so workers execute them at first too.
    open_files_ids
        .chain(rest_of_files)
        .enumerate()
        .filter(move |(i, _file)| i % WORKERS_THREAD_POOL_SIZE == worker)
        .map(|(_, file)| file)
        .collect()
}

type CalculatedAll = bool;

fn spawn_worker_tasks(
    files: Vec<FileBothFormats>,
    db: salsa::Snapshot<AnalysisDatabase>,
    trace_macro_diagnostics: bool,
    sender: Sender<(HashMap<Url, FileDiagnosticsChange>, CalculatedAll)>,
    file_diagnostics: HashMap<Url, FileDiagnostics>,
    diagnostics: &mut Diagnostics,
) {
    let notifier = diagnostics.notifier.clone();

    diagnostics.thread_pool.spawn(ThreadPriority::Worker, move || {
        let mut diff: HashMap<_, _> =
            files.iter().map(|file| (file.url.clone(), FileDiagnosticsChange::Unset)).collect();
        let mut calculated_all = true;

        for file in files {
            // Anything using salsa should be done in catch.
            let result = Backend::catch_cancellation(|| {
                let new_file_diagnostics = refresh_file_diagnostics(&db, file.id);
                let lsp_diagnostics =
                    to_lsp_diagnostics(&db, &new_file_diagnostics, trace_macro_diagnostics);

                (new_file_diagnostics, lsp_diagnostics)
            });

            match result {
                Ok((new_file_diagnostics, lsp_diagnostics)) => {
                    let diff_for_file = diff.get_mut(&file.url).unwrap();

                    if new_file_diagnostics.is_empty() {
                        *diff_for_file = FileDiagnosticsChange::Unset;

                        clear(&notifier, file.url);
                    } else if file_diagnostics.get(&file.url) == Some(&new_file_diagnostics) {
                        // No need to send same diagnostics twice.
                        *diff_for_file = FileDiagnosticsChange::Unchanged;
                    } else {
                        *diff_for_file =
                            FileDiagnosticsChange::Replaced(new_file_diagnostics.clone());

                        notifier.notify::<PublishDiagnostics>(PublishDiagnosticsParams {
                            uri: file.url,
                            diagnostics: lsp_diagnostics,
                            version: None,
                        });
                    }
                }
                Err(err) => {
                    calculated_all = false;

                    match err {
                        UnwindErrorKind::Canceled => {
                            // Any further iteration will fail to this branch anyway.
                            // So no need to execute them.
                            break;
                        }
                        UnwindErrorKind::Other => {
                            error!("caught error while calculating diagnostics");
                        }
                    }
                }
            }
        }

        sender.send((diff, calculated_all)).ok();
    });
}

/// Refresh diagnostics for a single file.
fn refresh_file_diagnostics(db: &AnalysisDatabase, file: FileId) -> FileDiagnostics {
    let modules_ids =
        if let Ok(modules_ids) = db.file_modules(file) { modules_ids } else { [].into() };
    let file_url = db.url_for_file(file);
    let mut semantic_file_diagnostics: Vec<SemanticDiagnostic> = vec![];
    let mut lowering_file_diagnostics: Vec<LoweringDiagnostic> = vec![];

    macro_rules! diags {
        ($db:ident. $query:ident($file_id:expr), $f:expr) => {
            trace_span!(stringify!($query)).in_scope(|| {
                catch_unwind(AssertUnwindSafe(|| $db.$query($file_id)))
                    .map($f)
                    .inspect_err(|_| {
                        error!("caught panic when computing diagnostics for file {file_url:?}");
                    })
                    .unwrap_or_default()
            })
        };
    }

    for module_id in modules_ids.iter() {
        semantic_file_diagnostics.extend(
            diags!(db.module_semantic_diagnostics(*module_id), Result::unwrap_or_default).get_all(),
        );
        lowering_file_diagnostics.extend(
            diags!(db.module_lowering_diagnostics(*module_id), Result::unwrap_or_default).get_all(),
        );
    }

    let parser_file_diagnostics = diags!(db.file_syntax_diagnostics(file), |r| r);

    FileDiagnostics {
        parser: parser_file_diagnostics,
        semantic: cairo_lang_diagnostics::Diagnostics::from_iter(semantic_file_diagnostics),
        lowering: cairo_lang_diagnostics::Diagnostics::from_iter(lowering_file_diagnostics),
    }
}

fn to_lsp_diagnostics(
    db: &AnalysisDatabase,
    new_file_diagnostics: &FileDiagnostics,
    trace_macro_diagnostics: bool,
) -> Vec<lsp_types::Diagnostic> {
    let mut diags = Vec::new();
    map_cairo_diagnostics_to_lsp(
        (*db).upcast(),
        &mut diags,
        &new_file_diagnostics.parser,
        trace_macro_diagnostics,
    );
    map_cairo_diagnostics_to_lsp(
        (*db).upcast(),
        &mut diags,
        &new_file_diagnostics.semantic,
        trace_macro_diagnostics,
    );
    map_cairo_diagnostics_to_lsp(
        (*db).upcast(),
        &mut diags,
        &new_file_diagnostics.lowering,
        trace_macro_diagnostics,
    );

    diags
}
