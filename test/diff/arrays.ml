(* Array literals: the elements are computed from the last to the first, as in OCaml. *)
let log = ref 0
let note d = log := (!log * 10) + d; d
let a = [| note 1; note 2; note 3 |]
let result = (!log * 1000) + (a.(0) * 100) + (a.(1) * 10) + a.(2)
