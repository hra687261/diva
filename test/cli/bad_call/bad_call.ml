(* `inv` requires `x <> 0`, and the top-level expression calls `inv 0`. The proof of
   `inv` works, but the obligation of the top-level expression fails. *)
let inv x = 100 / x
(*@ r = inv x
    requires x <> 0 *)

;; inv 0
