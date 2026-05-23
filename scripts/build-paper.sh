#!/usr/bin/env bash
# Build paper/paper.md to PDF using pandoc + a LaTeX engine.
# Usage: ./scripts/build-paper.sh [out.pdf]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${1:-$ROOT/paper/vapor.pdf}"
cd "$ROOT/paper"
pandoc paper.md \
  --citeproc \
  --bibliography references.bib \
  --pdf-engine=xelatex \
  -V geometry:margin=1in \
  -V documentclass=article \
  -V mainfont="Times" \
  -o "$OUT"
echo "wrote $OUT"
