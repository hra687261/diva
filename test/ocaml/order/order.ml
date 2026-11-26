(* OCaml computes the arguments of a call from the last to the first. So `g ()`
   raises `B` before `f ()` can raise `A`, and the result is 2. The translation binds
   the arguments by `let`, from the last to the first (`diva ocaml print`). *)
exception A
exception B

let f () : int = raise A
let g () : int = raise B
let sub a b = a - b

;; try sub (f ()) (g ()) with A -> 1 | B -> 2
