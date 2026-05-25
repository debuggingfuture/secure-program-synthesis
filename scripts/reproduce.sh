#!/usr/bin/env bash
# One-shot reproduction script for the Postern artifact.
# Builds Lean, runs the axiom audit, regenerates the corpus, runs
# the Rust unit tests and the conformance harness, and rebuilds the
# WASM bundle that /demo loads. Fails fast on the load-bearing
# steps (proofs + conformance); WASM is skipped with a notice if
# wasm-pack is not installed.
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

# Rebuild the WASM bundle that /demo loads, so a fresh clone can
# reproduce the interactive demo from source — not just the proofs.
# wasm-pack is the gating tool; if it isn't installed we report and
# skip rather than failing the whole reproduction (the proofs and
# the conformance harness above are the load-bearing claims).
if command -v wasm-pack >/dev/null 2>&1; then
  echo "==> WASM: rebuild postern-wasm for /demo"
  cd "$root"
  wasm-pack build prototype/crates/postern-wasm \
    --release --target web \
    --out-dir "$root/web/src/wasm" --out-name postern_wasm
  ls -l "$root/web/src/wasm/postern_wasm_bg.wasm"
else
  echo "==> WASM: skipping (wasm-pack not on PATH — install via 'cargo install wasm-pack' or 'brew install wasm-pack')"
fi

echo "==> All green."
