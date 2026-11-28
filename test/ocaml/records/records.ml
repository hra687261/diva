(* Records without mutable fields: a record is the tuple of its fields, in the order of
   its type. *)

type point = { x : int; y : int }
type segment = { from : point; upto : point }

let p = { y = 0; x = 3 }

(* `{ p with ... }`: the fields that aren't given are those of `p` *)
let q = { p with y = 2 }

(* `q.y` is 2: the division can't fail *)
let a = 10 / q.y

(* patterns on records, with fields left out *)
let manhattan { x; y } = abs x + abs y
let on_axis = function { x = 0; _ } | { y = 0; _ } -> true | _ -> false

(* records inside records *)
let s = { from = p; upto = q }
let len = manhattan { x = s.upto.x - s.from.x; y = s.upto.y - s.from.y }

(* mutable fields: each one is a ref. `{ c with ... }` copies the current value into a
   new ref, so `d.count` doesn't change when `c.count` does *)
type counter = { name : int; mutable count : int }

let c = { name = 1; count = 0 }
let () = c.count <- c.count + 1
let d = { c with name = 2 }
let () = c.count <- c.count + 1
let counts = match (c, d) with { count = n; _ }, { count = m; _ } -> (10 * n) + m

(* a parameter of type `int ref`. With `--entry bump`, `bump` gets a new ref that holds any
   integer: only the overflow of `!r + 1` is reported *)
let bump (r : int ref) = r := !r + 1
;;

((a + len + if on_axis p then 1 else 0) * 100) + counts
