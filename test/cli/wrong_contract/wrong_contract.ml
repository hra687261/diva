(* The contract is wrong: `sum 0` is `0`. Lean rejects the proof of `sum_body`. *)
let rec sum n = if n <= 0 then 0 else n + sum (n - 1)
(*@ r = sum n
    requires n >= 0
    ensures r > 0 *)

;; sum 10
