(* A field that is a ref is shared by a copy `{ r with ... }`, a mutable field isn't.
   And the field `contents` of the type `ref`. *)
type t = { shared : int ref; mutable own : int }

let a = { shared = ref 1; own = 2 }
let b = { a with own = a.own }

let () =
  b.shared := 10;
  b.own <- 20

let c = { contents = 5 }
let () = c.contents <- c.contents + 1
let d = match c with { contents = n } -> n
let e = match a with { shared = s; own } -> !s + own
let result = (!(a.shared) * 10000) + (a.own * 1000) + (d * 100) + e
