#!/usr/bin/env bash
# Reproduce the Lean check of the proof of OeisA370092.bounds
# (formal-conjectures pull request 4946, FormalConjectures/OEIS/370092.lean).
# Usage: bash check.sh /path/to/formal-conjectures
#   Tested with a formal-conjectures checkout at commit ab0addc45f699bdd0b7cc58efa5140a72f101a9e
#   (Lean v4.33.1); run `lake exe cache get` in the checkout first.
#   Statement.lean is the pull-request file, byte-identical (git blob 61345ec3...), compiled with the
#   repository's leanOptions. The Core files import Mathlib only.
set -euo pipefail
FC="$(cd "$1" && pwd)"
HERE="$(cd "$(dirname "$0")" && pwd)"
D=DMSolutions/OEIS_A370092
mkdir -p "$FC/$D"
cp "$HERE"/$D/*.lean "$FC/$D/"
cd "$FC"
O=.lake/build/lib/lean
mkdir -p "$O/$D"
echo "== formal-conjectures commit: $(git rev-parse HEAD)"
echo "== statement file git blob: $(git hash-object $D/Statement.lean)  (pull request 4946: 61345ec3...)"
# The repository's own leanOptions for the FormalConjectures library (lakefile.toml).
PKG="-Dpp.unicode.fun=true -DautoImplicit=false -DrelaxedAutoImplicit=false"
PKG="$PKG -Dweak.linter.style.copyright.formalConjectures=true -Dweak.linter.style.namespace=true"
PKG="$PKG -Dweak.linter.style.stubs=true -Dweak.linter.style.openClassical=true"
FCO="-Dwarn.sorry=false -Dweak.linter.style.ams_attribute=true -Dweak.linter.style.category_attribute=true"
FCO="$FCO -Dweak.linter.style.category_answer=true -Dweak.linter.style.conditional_formal_proof=true"
FCO="$FCO -Dweak.linter.style.moduleDocstring=true -Dweak.linter.style.latex_docstring=true"
FCO="$FCO -Dweak.linter.style.imports=true -Dweak.google.answer=always_true"
echo "== 1. Statement.lean (unmodified pull-request file, repository options)"
lake env lean $PKG $FCO -o "$O/$D/Statement.olean" $D/Statement.lean
for f in CoreDefs CoreClosed CoreArith CoreTwoAdic CoreOdd Core Solution; do
  echo "== compiling $f.lean"
  lake env lean -o "$O/$D/$f.olean" $D/$f.lean
done
echo "== CheckAnswer.lean (definitions agree; type of bounds_solved = type of bounds; axioms)"
lake env lean $D/CheckAnswer.lean
echo "== forbidden keywords (sorry/admit/native_decide/axiom) outside the statement file:"
FILES=""
for f in CoreDefs CoreClosed CoreArith CoreTwoAdic CoreOdd Core Solution CheckAnswer; do FILES="$FILES $D/$f.lean"; done
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' $FILES || echo "none"
echo "== done"
