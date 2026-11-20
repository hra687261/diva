(* No runtime error, though the program divides: the analysis proves the divisors
   are not zero. *)

let rec g n x = if n <= 0 then x else g (n - 1) (x * x + 1)

let d = g 3 1                 (* x starts at 1, and x * x + 1 >= 1 > 0 *)
let q = 100 / d               (* never divides by zero *)

let pos x = if x > 0 then x else 1   (* always positive *)
let r = 60 / pos (0 - 5)
;;
q + r
