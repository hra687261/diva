#!/usr/bin/env bash
# A stand-in for an LLM, for `diva spec --oracle ./llm.sh`. It reads the question on
# its standard input. Its first contract for `double` is false: `double (-1)` is -2.
# When the question says that it was rejected, it adds `requires x >= 0`.
question=$(cat)
if grep -q "previous answer was rejected" <<<"$question"; then
  requires='"    requires x >= 0",'
else
  requires=""
fi
cat <<JSON
{"program": [
  "let double x = x + x",
  "(*@ r = double x",
  $requires
  "    ensures r >= 0 *)",
  "",
  "let quad x = double (double x)",
  "(*@ r = quad x",
  "    requires x >= 0",
  "    ensures r >= 0 *)",
  "",
  ";; quad 3"]}
JSON
