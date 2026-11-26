(* overflow *)
(* `Int32` has 32 bits *)
let result = Int32.to_int (Int32.add Int32.max_int 1l)
