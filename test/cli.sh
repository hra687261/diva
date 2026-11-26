#!/usr/bin/env bash
# End-to-end tests of `diva`. Run from the repository root: test/cli.sh [--update]
#
# Each `test/cli/<folder>/<name>.ml` is a test, one per folder. It is copied to a
# temporary folder, and each command of `commands` is run on it there. The outputs and
# exit codes go to `<name>.out`. `cert` writes the certificate `<name>.lean`, and `prove`
# writes `prove.lean`. The temporary folder is compared with the test's folder. A missing
# `<name>.out` is created. `--update` rewrites all of them.
#
# A test's folder may also have a file `commands`, with more commands to run, one per
# line, and scripts `*.sh` that these commands use.
#
# The tests in `test/ocaml/` are the same, but every command is run as `diva ocaml CMD`:
# they are read by the OCaml frontend. Then `test/diff.sh` runs the programs of
# `test/diff/` under OCaml and under DIVA, and compares their results.
set -u
export PATH=$HOME/.elan/bin:$PATH
lake build diva >/dev/null || exit 1
# the OCaml frontend, if dune is installed (`nix develop`). Without it, the tests in
# `test/ocaml/` are skipped.
if command -v dune >/dev/null; then frontend/ocaml/build.sh || exit 1; fi
diva=$PWD/.lake/build/bin/diva
commands=(run check opt hints "cert --check" "prove --check -o prove.lean")
fails=0

# The output of each command on the program $1, run from its folder. $2 is put before
# each command: `ocaml` or nothing.
outputs() {
  local all=("${commands[@]}")
  if [ -f "$(dirname "$1")/commands" ]; then
    mapfile -t -O "${#all[@]}" all <"$(dirname "$1")/commands"
  fi
  for command in "${all[@]}"; do
    command="$2$command"
    echo "\$ diva $command $(basename "$1")"
    # `$command` unquoted: `cert --check` is two arguments
    (cd "$(dirname "$1")" && "$diva" $command "$(basename "$1")" 2>&1)
    echo "[exit $?]"
    echo
  done
}

for test in $(find test/cli test/ocaml -name "*.ml" | sort); do
  dir=$(dirname "$test")
  prefix=""
  if [ "${test#test/ocaml/}" != "$test" ]; then
    prefix="ocaml "
    if [ ! -x .lake/build/bin/ocaml-frontend ]; then
      echo "skip $test (no OCaml)"
      continue
    fi
  fi
  work=$(mktemp -d)
  cp "$test" "$work"
  cp "$dir"/commands "$dir"/*.sh "$work" 2>/dev/null
  outputs "$work/$(basename "$test")" "$prefix" >"$work/$(basename "${test%.ml}").out"
  if [ "${1:-}" = "--update" ] || [ ! -f "${test%.ml}.out" ]; then
    rm -f "$dir"/*.lean
    cp "$work"/* "$dir"
    echo "wrote $dir"
  elif d=$(diff -ruN "$dir" "$work"); then
    echo "ok   $test"
  else
    echo "FAIL $test"
    echo "$d"
    fails=$((fails + 1))
  fi
  rm -rf "$work"
done

# the differential tests, if OCaml is installed
if [ -x .lake/build/bin/ocaml-frontend ] && command -v ocaml >/dev/null; then
  test/diff.sh || fails=$((fails + 1))
else
  echo "skip test/diff (no OCaml)"
fi

[ "$fails" -eq 0 ] && echo "all passed" || { echo "$fails failed"; exit 1; }
