#!/usr/bin/env bash
# End-to-end tests of `diva`. Run from the repository root: test/cli.sh [--update]
#
# Each `test/cli/<folder>/<name>.ml` is a test, one per folder. It is copied to a
# temporary folder, and each command of `commands` is run on it there. The outputs and
# exit codes go to `<name>.out`, and `cert` writes the certificate `<name>.lean`. The
# temporary folder is compared with the test's folder. A missing `<name>.out` is
# created. `--update` rewrites all of them.
set -u
export PATH=$HOME/.elan/bin:$PATH
lake build diva >/dev/null || exit 1
diva=$PWD/.lake/build/bin/diva
commands=(run check opt hints "cert --check")
fails=0

# The output of each command on the program $1, run from its folder.
outputs() {
  for command in "${commands[@]}"; do
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
  outputs "$work/$(basename "$test")" >"$work/$(basename "${test%.ml}").out"
  if [ "${1:-}" = "--update" ] || [ ! -f "${test%.ml}.out" ]; then
    rm -f "${test%.ml}.lean"
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
