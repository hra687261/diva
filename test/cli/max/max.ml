(* Contracts on functions with several parameters are not supported yet. *)
let max a b = if a < b then b else a
(*@ r = max a b
    ensures r >= a && r >= b *)

;; max 1 2
