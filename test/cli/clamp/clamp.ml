(* No function has a contract. `diva spec --oracle ./llm.sh` asks the mock LLM
   `llm.sh` for the contract of `clamp`. *)
let clamp x = if x < 0 then 0 else if x > 100 then 100 else x

;; clamp 150
