#!/usr/bin/env bash
# A stand-in for an LLM, for `diva prove --oracle ./llm.sh`. It reads the question on
# its standard input, and answers with a proof that uses the axiom `sorryAx`.
cat >/dev/null
cat <<'JSON'
{"proof": [
  "intro va μ ⟨x, hva, hpre⟩",
  "subst hva",
  "simp [square_fn, wp, BinOp.denote, List.lookup, callEnv]",
  "exact sorryAx _ false"]}
JSON
