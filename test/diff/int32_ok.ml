(* `Int32` and `Int64` without overflow *)
let result =
  Int32.to_int (Int32.mul 1000l 1000l) + Int64.to_int (Int64.sub 5000000000L 4999999999L)
