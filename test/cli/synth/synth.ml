(* `abs` has a contract but no code. `diva synth --oracle ./llm.sh` asks the mock
   LLM `llm.sh` for the code. *)
let abs x = assert false
(*@ r = abs x
    ensures r >= 0 && r >= x && r >= 0 - x *)

;; abs (0 - 7)
