(* `half` and `inv` have no contract, and `f` calls them. `diva prove` gives them the
   empty contract: on integers, they don't fail. `half` can't fail, so its proof
   works. `inv 0` divides by zero, so its proof fails. `unused` isn't called by a
   function with a contract, so it gets no contract. *)
let half x = x / 2

let inv x = 100 / x

let unused x = 1 / 0

let f x = half x + inv x
(*@ r = f x *)

;; f 3
