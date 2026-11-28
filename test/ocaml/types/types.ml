(* Entry points. Nothing calls these functions: without `--entry` they never run, so they
   can't fail. With `--entry`, each one is checked for all the arguments of its type: no "may
   not be a boolean" or "may not match a list". What remains is real: `w * h` and `x + 1`
   overflow for some integers. *)

type shape = Circle of int | Rect of int * int

let negate b = if b then false else true
let area s = match s with Circle r -> r | Rect (w, h) -> w * h
let first l = match l with x :: _ -> x + 1 | [] -> 0
let code c = Char.code c + 1

(* `quad` and `half` both use `div2`, which is analysed once, by its summary *)
let rec div2 n = if n < 2 then 0 else 1 + div2 (n - 2)
let quad n = div2 n * 4
let half n = div2 n

(* the top-level code runs before `inv` is called: `inv` divides by zero *)
let r = ref 1
let () = r := 0
let inv x = x / !r

(* refs given by other code, and refs of refs: each one is a new ref of the entry
   point's call, whose contents have the type of the ref *)
let bump2 (r : int ref ref) = !r := !(!r) + 1
let reset (r : int ref ref) = r := ref 0

(* this one fails: the top-level code always runs, with or without `--entry` *)
let z = 10 / 0
