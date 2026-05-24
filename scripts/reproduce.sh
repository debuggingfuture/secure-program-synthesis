#!/usr/bin/env bash
# One-shot reproduction script for the Postern artifact.
# Builds Lean, audits axioms, emits the corpus, then runs the Rust
# unit tests and differential harness. Fails fast.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"

echo "==> Lean: build + axiom audit"
cd "$root/verifier/lean"
lake build

echo "==> Lean: emit differential-test corpus"
lake exe postern-corpus > "$root/prototype/corpus/postern-corpus.json"
wc -c "$root/prototype/corpus/postern-corpus.json"

echo "==> Rust: unit tests"
cd "$root/prototype"
cargo test --workspace --quiet

echo "==> Differential test: Lean reference vs. Rust impl"
cargo run -p postern-diff --quiet -- corpus/postern-corpus.json

echo "==> All green."
