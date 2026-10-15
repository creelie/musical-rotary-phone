#!/usr/bin/env bash
# make_figures.sh -- draw the three figures of the paper and write them to
# paper/figures/ as PNG at 200 dpi.  Needs pdflatex (with TikZ) and pdftoppm.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
OUT=../paper/figures
mkdir -p "$OUT"
for f in fig_roadmap fig_greedy fig_chains; do
  pdflatex -interaction=nonstopmode -halt-on-error "$f.tex" > /dev/null
  pdftoppm -r 200 -png -singlefile "$f.pdf" "$OUT/$f"
  rm -f "$f.aux" "$f.log"
done
ls -l "$OUT"
