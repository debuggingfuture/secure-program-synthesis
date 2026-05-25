#!/usr/bin/env bash
# Render paper.md to paper.pdf via Pandoc + BibTeX. Requires pandoc +
# a TeX engine. Default engine is tectonic (self-contained, auto-fetches
# packages); override via PDF_ENGINE=xelatex / lualatex if you prefer a
# full TeX Live install. header.tex carries a couple of small shims so
# the build doesn't depend on the full hyperxmp / unicode-math stack.
set -euo pipefail

cd "$(dirname "$0")"

if ! command -v pandoc >/dev/null 2>&1; then
  echo "pandoc not on PATH. brew install pandoc (macOS)" >&2
  exit 1
fi

PDF_ENGINE="${PDF_ENGINE:-tectonic}"
if ! command -v "$PDF_ENGINE" >/dev/null 2>&1; then
  echo "$PDF_ENGINE not on PATH. brew install tectonic (or mactex-no-gui for xelatex)" >&2
  exit 1
fi

# Re-render mermaid figures to both PDF (for tectonic) and SVG (for the
# web /paper renderer, since browsers don't display PDFs in <img> tags).
# Source of truth is the .mmd; PDF + SVG are derived. mmdc is invoked via
# npx so contributors don't need a global install.
for src in figures/*.mmd; do
  [ -f "$src" ] || continue
  base="${src%.mmd}"
  npx -y -p @mermaid-js/mermaid-cli mmdc -i "$src" -o "$base.pdf" -b transparent >/dev/null
  npx -y -p @mermaid-js/mermaid-cli mmdc -i "$src" -o "$base.svg" -b transparent >/dev/null
done

pandoc paper.md \
  --citeproc \
  --bibliography=references.bib \
  --pdf-engine="$PDF_ENGINE" \
  --metadata link-citations=true \
  --include-in-header=header.tex \
  -o paper.pdf

echo "wrote $(pwd)/paper.pdf"

# Mirror to the web site's public/ so the landing page can link to the
# hosted PDF at /paper.pdf and the /paper renderer can <img>-embed the
# SVG figures at /figures/*.svg. The web build (`pnpm --filter web
# build`) copies anything under public/ verbatim to dist/.
WEB_PUBLIC="$(cd .. && pwd)/web/public"
if [ -d "$WEB_PUBLIC" ]; then
  cp paper.pdf "$WEB_PUBLIC/paper.pdf"
  mkdir -p "$WEB_PUBLIC/figures"
  for svg in figures/*.svg; do
    [ -f "$svg" ] || continue
    cp "$svg" "$WEB_PUBLIC/figures/"
  done
  echo "mirrored to $WEB_PUBLIC/paper.pdf + $WEB_PUBLIC/figures/"
fi
