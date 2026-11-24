(* Functions with several parameters. `mul` is recursive, with two parameters.
   `max3` has three, and calls `max` twice. `area` calls `mul`. *)
let rec mul a b = if b <= 0 then 0 else a + mul a (b - 1)
(*@ r = mul a b
    requires a >= 0
    ensures r >= 0 *)

let max a b = if a < b then b else a
(*@ r = max a b
    ensures r >= a && r >= b *)

let max3 a b c = max (max a b) c
(*@ r = max3 a b c
    ensures r >= a && r >= b && r >= c *)

let area w h = mul (max w 0) h
(*@ r = area w h
    ensures r >= 0 *)

;; area (max3 1 5 2) 3
