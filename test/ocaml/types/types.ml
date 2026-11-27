(* The types of the parameters, as hints. Nothing calls these functions, so the analysis
   assumes that their parameters have their types: no "may not be a boolean" or "may not
   match a list". What remains is real: `w * h` and `x + 1` overflow for some integers. *)

type shape = Circle of int | Rect of int * int

let negate b = if b then false else true
let area s = match s with Circle r -> r | Rect (w, h) -> w * h
let first l = match l with x :: _ -> x + 1 | [] -> 0
let code c = Char.code c + 1

(* this one fails, so `check` looks at the whole program *)
let z = 10 / 0
