(* The mock LLM `llm.sh` proves `x * x >= 0` with `exact sorryAx _ false`. It has no
   forbidden word, so `diva` writes it in the file, and Lean accepts it. But the proof
   uses the axiom `sorryAx`, so `diva` rejects it. *)
let square x = x * x
(*@ r = square x
    ensures r >= 0 *)

;; square 3
