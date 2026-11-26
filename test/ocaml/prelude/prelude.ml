(* Functions of the standard library, from DIVA's prelude (`frontend/ocaml/prelude.ml`).
   Only those that the program uses are added. A function that the prelude doesn't have,
   such as `List.sort`, is rejected. *)

let l = [ 3; 1; 2 ]
let n = List.length l
let s = List.fold_left ( + ) 0 l
let m = List.map (fun x -> x * 2) l
let r = List.rev (l @ [ 4 ])
let f = fst (1, 2) + snd (3, 4) + abs (-5) + min 1 2 + max 3 4
let h = List.hd l
let o = Option.get (Some 1)
let () = print_int (n + s + List.nth m 0 + List.hd r + f + h + o)
