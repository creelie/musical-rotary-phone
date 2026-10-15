#!/usr/bin/env bash
# make_figures.sh -- draw the three figures of the paper and write them to
# paper/figures/ as PNG at 200 dpi.  Needs pdflatex (with TikZ and pgfplots),
# pdftoppm and python3 (for the data of the third figure).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
OUT=../paper/figures
mkdir -p "$OUT"
[ -s ratio.dat ] || python3 ratio_data.py 10000000 ratio.dat
for f in fig_greedy fig_chains fig_ratio; do
  pdflatex -interaction=nonstopmode -halt-on-error "$f.tex" > /dev/null
  pdftoppm -r 200 -png -singlefile "$f.pdf" "$OUT/$f"
  rm -f "$f.aux" "$f.log"
done
ls -l "$OUT"
