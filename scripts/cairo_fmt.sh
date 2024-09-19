#!/bin/bash

cargo run --profile=ci-dev --bin cairo-format -- -s --recursive "$@" corelib/stdlib/cairo/array.cairo
