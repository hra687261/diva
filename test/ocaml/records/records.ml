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
;;

a + len + if on_axis p then 1 else 0
