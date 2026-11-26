#!/usr/bin/env bash
# Differential tests of `diva ocaml`: each `test/diff/<name>.ml` ends with
# `let result = ...`, and OCaml and `diva ocaml run` must give the same result: a value,
# `exception E`, or `overflow` for a failed overflow check of DIVA. In a program with the
# comment `(* overflow *)`, OCaml's result wraps around, and DIVA must give `overflow`.
# Run from the repository root, in `nix develop` (it needs `ocaml` and the OCaml frontend).
set -u
diva_exe=$PWD/.lake/build/bin/diva

# OCaml's toplevel prints `val result : int = 38` or `Exception: Neg (-2).`
ocaml_result() {
  printf '#use "%s";;\n' "$1" | ocaml -noprompt -color=never 2>&1 |
    sed -n 's/^val result : [a-z]* = //p; s/^Exception: \([A-Za-z_]*\).*/exception \1/p'
}

# DIVA prints `38`, `runtime error: uncaught exception (Neg -2)` or
# `runtime error: assertion failed`
diva_result() {
  "$diva_exe" ocaml run "$1" 2>&1 |
    sed 's/^runtime error: uncaught exception (*\([A-Za-z_]*\).*/exception \1/
         s/^runtime error: assertion failed$/overflow/'
}

fails=0
for test in test/diff/*.ml; do
  name=$(basename "$test" .ml)
  ocaml=$(ocaml_result "$test")
  diva=$(diva_result "$test")
  expected=$ocaml
  grep -q '(\* overflow \*)' "$test" && expected=overflow
  if [ "$diva" = "$expected" ]; then
    echo "ok   $name: $diva"
  else
    echo "FAIL $name: OCaml gives $ocaml, DIVA gives $diva"
    fails=$((fails + 1))
  fi
done
[ "$fails" -eq 0 ] && echo "all agree" || { echo "$fails disagree"; exit 1; }

# TODO: use dune or something else to run the tests
# TODO: run check/prove etc on these tests as well