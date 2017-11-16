#! /usr/bin/env bash
#
# File: build.sh
#
# Created: 25 November 2016
#

# treat undefined variable substitutions as errors
set -u
# propagate errors from all parts of pipes
set -o pipefail

# ./.cabal-sandbox/bin/lhs2TeX Talk.lhs -o Talk.tex --poly # && pdflatex -shell-escape Talk.tex
# lhs2TeX Talk.lhs -o Talk.tex --poly && pdflatex -shell-escape Talk.tex
lhs2TeX Talk.lhs -o Talk.tex --tt && pdflatex -shell-escape Talk.tex

exit 0

