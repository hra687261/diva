(* `quad` has a contract, and calls `double`, which has none. So `diva prove` can't
   prove the contract of `quad`. `diva spec --oracle ./llm.sh` asks the mock LLM
   `llm.sh` for the contract of `double`. *)
let double x = x + x

let quad x = double (double x)
(*@ r = quad x
    requires x >= 0
    ensures r >= 0 *)

;; quad 3
