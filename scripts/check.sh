#!/bin/bash

set -e
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo build --verbose --locked
cargo test --verbose
