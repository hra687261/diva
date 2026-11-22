#!/usr/bin/env bash
# A stand-in for an LLM, for `diva prove --oracle ./llm.sh`. It reads the question on
# its standard input. Its first answer is text, so it is rejected. Its second proof
# fails in Lean. When the question shows that proof in the file, it answers with a
# proof that works.
question=$(cat)
if grep -q "  grind" <<<"$question"; then
  cat <<'JSON'
{"proof": [
  "intro va μ ⟨x, hva, hpre⟩",
  "subst hva",
  "simp [square_fn, wp, BinOp.denote, List.lookup, callEnv]",
  "rcases Int.le_total 0 x with h | h",
  "· exact Int.mul_nonneg h h",
  "· exact Int.mul_nonneg_of_nonpos_of_nonpos h h"]}
JSON
elif grep -q "not only JSON" <<<"$question"; then
  cat <<'JSON'
{"proof": [
  "intro va μ ⟨x, hva, hpre⟩",
  "subst hva",
  "simp [square_fn, wp, BinOp.denote, List.lookup, callEnv]",
  "grind"]}
JSON
else
  echo "Here is a proof: grind"
fi
