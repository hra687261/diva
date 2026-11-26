(* OCaml computes the arguments from the last to the first: `g ()` raises first *)
exception A
exception B
let f () = raise A
let g () = raise B
let result = (fun a b -> a + b) (f ()) (g ())
