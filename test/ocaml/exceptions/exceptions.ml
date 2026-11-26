(* Exceptions: `raise`, `try`, `failwith`, and a `match` on an exception. *)

exception Neg of int
exception Too_big

(* raises `Neg` on a negative number, `Too_big` above 100 *)
let check x = if x < 0 then raise (Neg x) else if x > 100 then raise Too_big else x

(* every exception of `check` is caught *)
let clamp x = try check x with Neg _ -> 0 | Too_big -> 100

(* the handler uses the argument of `Neg` *)
let fix x = try check x with Neg n -> 0 - n | Too_big -> 100

(* `failwith` raises `Failure` *)
let half x = if x mod 2 = 0 then x / 2 else failwith "odd"
let half_or_zero x = try half x with Failure _ -> 0

let () =
  print_int (clamp (-5) + clamp 50 + clamp 500 + fix (-3) + half_or_zero 7 + half_or_zero 8)
