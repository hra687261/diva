(* the same exception *)
exception Neg of int
let check x = if x < 0 then raise (Neg x) else x
let result = check 3 + check (-2)
