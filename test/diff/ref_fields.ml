(* A field that is a ref is shared by a copy `{ r with ... }`. And the field `contents`
   of the type `ref`. *)
type t = { shared : int ref; id : int }

let a = { shared = ref 1; id = 2 }
let b = { a with id = 3 }
let () = b.shared := 10
let c = { contents = 5 }
let () = c.contents <- c.contents + 1
let d = match c with { contents = n } -> n
let e = match a with { shared = s; id } -> !s + id
let result = (!(a.shared) * 10000) + (b.id * 1000) + (d * 100) + e
