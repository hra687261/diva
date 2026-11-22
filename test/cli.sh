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
set -u
export PATH=$HOME/.elan/bin:$PATH
lake build diva >/dev/null || exit 1
diva=$PWD/.lake/build/bin/diva
commands=(run check opt hints "cert --check" "prove --check -o prove.lean")
fails=0

# The output of each command on the program $1, run from its folder.
outputs() {
  local all=("${commands[@]}")
  if [ -f "$(dirname "$1")/commands" ]; then
    mapfile -t -O "${#all[@]}" all <"$(dirname "$1")/commands"
  fi
  for command in "${all[@]}"; do
    echo "\$ diva $command $(basename "$1")"
    # `$command` unquoted: `cert --check` is two arguments
    (cd "$(dirname "$1")" && "$diva" $command "$(basename "$1")" 2>&1)
    echo "[exit $?]"
    echo
  done
}

for test in $(find test/cli -name "*.ml" | sort); do
  dir=$(dirname "$test")
  work=$(mktemp -d)
  cp "$test" "$work"
  cp "$dir"/commands "$dir"/*.sh "$work" 2>/dev/null
  outputs "$work/$(basename "$test")" >"$work/$(basename "${test%.ml}").out"
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

[ "$fails" -eq 0 ] && echo "all passed" || { echo "$fails failed"; exit 1; }
