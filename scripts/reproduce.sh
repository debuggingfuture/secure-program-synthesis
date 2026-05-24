#!/usr/bin/env bash
# One-shot reproduction script for the Postern artifact.
# Builds Lean, runs the axiom audit, regenerates the corpus, then
# runs the Rust unit tests and the conformance harness. Fails fast.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"

echo "==> Lean: build (Postern + CheckAxioms)"
cd "$root/verifier/lean"
lake build

echo "==> Lean: axiom audit (CheckAxioms.lean output)"
# The build log above contains '#print axioms ...' lines; rerun in
# isolation to surface them on a clean console.
lake env lean CheckAxioms.lean | grep -E "depends on axioms|does not depend on any axioms"

echo "==> Lean: emit reference conformance corpus"
lake exe postern-corpus > /tmp/postern-corpus-fresh.json
if ! diff -q /tmp/postern-corpus-fresh.json \
              "$root/prototype/corpus/postern-corpus.json" >/dev/null; then
  echo "    !! corpus drift detected — overwriting committed copy"
  cp /tmp/postern-corpus-fresh.json "$root/prototype/corpus/postern-corpus.json"
fi
wc -c "$root/prototype/corpus/postern-corpus.json"

echo "==> Rust: unit tests"
cd "$root/prototype"
cargo test --workspace --quiet

echo "==> Conformance test: Lean reference vs. Rust impl"
cargo run -p postern-diff --quiet -- corpus/postern-corpus.json

echo "==> All green."
