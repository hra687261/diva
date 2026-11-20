#!/usr/bin/env bash
# End-to-end tests of `diva`. Run from the repository root: test/cli.sh [--update]
#
# Each `test/cli/**/<name>.ml` is a test. Each command of `commands` is run on it,
# and the outputs and exit codes are compared with `<name>.out`, next to it. A
# missing `<name>.out` is created. `--update` rewrites all of them.
set -u
export PATH=$HOME/.elan/bin:$PATH
lake build diva >/dev/null || exit 1
diva=$PWD/.lake/build/bin/diva
commands="run check opt hints"
fails=0

# The output of each command on the program $1, run from its folder.
outputs() {
  for command in $commands; do
    echo "\$ diva $command $(basename "$1")"
    (cd "$(dirname "$1")" && "$diva" "$command" "$(basename "$1")" 2>&1)
    echo "[exit $?]"
    echo
  done
}

for test in $(find test/cli -name "*.ml" | sort); do
  file=${test%.ml}.out
  if [ "${1:-}" = "--update" ] || [ ! -f "$file" ]; then
    outputs "$test" >"$file"
    echo "wrote $file"
  elif d=$(diff -u "$file" <(outputs "$test")); then
    echo "ok   $test"
  else
    echo "FAIL $test"
    echo "$d"
    fails=$((fails + 1))
  fi
done

[ "$fails" -eq 0 ] && echo "all passed" || { echo "$fails failed"; exit 1; }
