#!/bin/sh
# Build doc/discrepancies.pdf -- the version of doc/discrepancies.md that goes
# to the authors, typeset in the paper's own notation.
#
# The .tex is hand-written rather than generated from the .md on purpose: the
# note is full of mathematics, and converting the markdown's code spans gives
# typewriter formulae, which is exactly what a reader of the paper should not
# get.  KEEP THE TWO IN SYNC when the findings change.
set -e
cd "$(dirname "$0")/../doc"
pdflatex -interaction=nonstopmode discrepancies.tex > /dev/null
pdflatex -interaction=nonstopmode discrepancies.tex > /dev/null
rm -f discrepancies.aux discrepancies.log discrepancies.out discrepancies.toc
echo "doc/discrepancies.pdf written ($(pdfinfo discrepancies.pdf | awk '/^Pages/{print $2}') pages)"
