#!/bin/bash
set -e
cd "$(dirname "$0")"
echo "=== Building randomized-svd ==="
cargo build --quiet 2>&1
echo "=== Running tests ==="
cargo test --quiet 2>&1
echo "=== All tests passed ==="
