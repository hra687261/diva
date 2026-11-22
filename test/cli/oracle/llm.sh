#!/usr/bin/env bash
# A stand-in for an LLM, for `diva check --oracle ./llm.sh`. It reads the question on
# its standard input. It runs once per question, so it learns what happened from the
# question only:
# - first, it answers with text, which isn't in the format, so `diva` rejects it
# - when told that its answer isn't in the format, it gives a wrong fact, which the
#   checker rejects
# - when told that the checker rejected its fact, it gives the right fact.
question=$(cat)
if grep -q "the checker rejected" <<<"$question"; then
  echo '{"facts": [{"about": "$f#0", "holds": "-5 <= v && v <= -4"}]}'
elif grep -q "isn't in the format" <<<"$question"; then
  echo '{"facts": [{"about": "$f#0", "holds": "-4 <= v && v <= -1"}]}'
else
  echo 'I think `f` returns a value between -4 and -1.'
fi
