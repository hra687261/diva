(* Records with mutable fields: aliasing, and `{ r with ... }` copies the fields. *)
type acc = { id : int; mutable total : int; mutable last : int }

let add a v =
  a.total <- a.total + v;
  a.last <- v

let a = { id = 1; total = 0; last = 0 }
let b = a
let c = { a with id = 2 }
let () = add b 5
let () = add c 7
let result = (a.total * 10000) + (a.last * 1000) + (c.total * 10) + c.last
