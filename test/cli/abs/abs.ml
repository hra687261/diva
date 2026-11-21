(* `abs` is not recursive. `dist` calls `abs`, and its contract has no header, so
   the result is named `result`. *)
let abs x = if x < 0 then 0 - x else x
(*@ r = abs x
    ensures r >= 0 && r >= x && r >= 0 - x *)

let dist a = abs (a - 10)
(*@ ensures result >= 0 *)

;; dist 3
