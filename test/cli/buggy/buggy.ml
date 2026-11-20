(* A program the checker rejects, pointing at the culprits. *)

let rec count l = match l with [] -> 0 | _ :: t -> 1 + count t

let rec sum l = match l with [] -> 0 | x :: xs -> x + sum xs

let average l = sum l / count l

let a = average [1; 2; 3]
let b = average []             (* division by zero at run time *)
;;
a + b
