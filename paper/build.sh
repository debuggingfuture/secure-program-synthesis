#!/usr/bin/env bash
# Render paper.md to paper.pdf via Pandoc + BibTeX. Requires pandoc +
# a TeX distribution (texlive-xetex on Linux, mactex / basictex on
# macOS). No-op-friendly: if pandoc is missing we print a hint and
# exit non-zero so CI can detect the missing dep.
set -euo pipefail

cd "$(dirname "$0")"

if ! command -v pandoc >/dev/null 2>&1; then
  echo "pandoc not on PATH. brew install pandoc basictex (macOS)" >&2
  exit 1
fi

pandoc paper.md \
  --citeproc \
  --bibliography=references.bib \
  --pdf-engine=xelatex \
  --metadata link-citations=true \
  -o paper.pdf

echo "wrote $(pwd)/paper.pdf"
