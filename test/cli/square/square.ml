(* `omega` can't prove `x * x >= 0`, so `diva prove --check` fails. With
   `--oracle ./llm.sh`, the mock LLM `llm.sh` writes the proof. *)
let square x = x * x
(*@ r = square x
    ensures r >= 0 *)

;; square 3
