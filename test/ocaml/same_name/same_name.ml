(* DIVA tells constructors apart by their names only: two constructors with the same
   name are rejected. *)
type a = A of int | B
type b = A | C

let x = (A : b)
let y = (A 1 : a)
