#!/usr/bin/env bash
# A stand-in for an LLM, for `diva spec --oracle ./llm.sh`. It reads the question on
# its standard input. Its first contract is false: `clamp 150` is 100, not 150. When
# the question says that it was rejected, it gives a true contract.
question=$(cat)
if grep -q "previous answer was rejected" <<<"$question"; then
  ensures="r >= 0 && r <= 100"
else
  ensures="r >= 0 && r <= 100 && r >= x"
fi
cat <<JSON
{"program": [
  "let clamp x = if x < 0 then 0 else if x > 100 then 100 else x",
  "(*@ r = clamp x",
  "    ensures $ensures *)",
  "",
  ";; clamp 150"]}
JSON
