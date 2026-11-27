(* Contracts with booleans and lists in an OCaml file. *)

let both a b = a && b
(*@ r = both a b ensures r = (a && b) *)

(* `requires` bounds the length: then `1 + length t` can't overflow *)
let rec length l = match l with [] -> 0 | _ :: t -> 1 + length t
(*@ r = length l requires List.length l <= 100 ensures r = List.length l *)

let has_two l = match l with _ :: _ :: _ -> true | _ -> false
(*@ r = has_two l ensures r = (List.length l >= 2) *)

let () = if both true (has_two [ 3; 4 ]) then print_int (length [ 1; 2 ])
