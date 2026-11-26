#!/usr/bin/env bash
# Build the OCaml front end with dune, and copy it to .lake/build/bin/ocaml-frontend,
# next to `diva`. Needs OCaml 5.4 and dune (`nix develop` gives them).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out="$here/../../.lake/build/bin"
dune build --root "$here" ./frontend.exe
mkdir -p "$out"
cp -f "$here/_build/default/frontend.exe" "$out/ocaml-frontend"
