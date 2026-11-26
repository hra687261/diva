(* a handler that matches some exceptions only *)
exception E of int
let f x = if x > 0 then raise (E x) else if x < 0 then raise Not_found else 0
let g x = try f x with E n -> n * 2
let result = g 5 + g 0 + (try g (-1) with Not_found -> 100)
