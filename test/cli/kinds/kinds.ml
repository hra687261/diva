(* Contracts with booleans (`not`, `||`) and lists (`length l`). The kind of each name
   comes from how the contract uses it. `prove` proves all the obligations. *)

let pick b x y = if b then x else y
(*@ r = pick b x y requires b || x = y ensures r = x *)

let negate b = if b then false else true
(*@ r = negate b ensures r = not b *)

let is_empty l = match l with [] -> true | _ :: _ -> false
(*@ r = is_empty l ensures r = (length l = 0) *)

let at_least_two l = match l with [] -> 0 | _ :: t -> (match t with [] -> 1 | _ :: _ -> 2)
(*@ r = at_least_two l requires length l >= 2 ensures r = 2 *)

;; pick (negate false) 1 2 + at_least_two [3; 4] + (if is_empty [] then 1 else 0)
