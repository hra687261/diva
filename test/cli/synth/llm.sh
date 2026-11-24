#!/usr/bin/env bash
# A stand-in for an LLM, for `diva synth --oracle ./llm.sh`. It reads the question on
# its standard input.
# - First, it weakens the contract: `diva` rejects the answer.
# - When the question says so, it writes wrong code: Lean rejects it.
# - When the question shows Lean's errors, it writes the right code.
question=$(cat)
if grep -q "error:" <<<"$question"; then
  code="if x < 0 then 0 - x else x"
  ensures="r >= 0 && r >= x && r >= 0 - x"
elif grep -q "it changes the program" <<<"$question"; then
  code="x"
  ensures="r >= 0 && r >= x && r >= 0 - x"
else
  code="x"
  ensures="r >= x"
fi
cat <<JSON
{"program": [
  "let abs x = $code",
  "(*@ r = abs x",
  "    ensures $ensures *)",
  "",
  ";; abs (0 - 7)"]}
JSON
