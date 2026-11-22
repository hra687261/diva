(* `f 0` is -5, but the inference finds that `f` returns a value in [-5, +∞], so
   `diva check` says the division may fail. `llm.sh` proposes the result of `f`. *)
let rec f n = if n >= 100 then n - 105 else f (n + 2) ;;
10 / f 0
