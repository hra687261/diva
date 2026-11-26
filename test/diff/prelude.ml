(* the functions of the prelude *)
let l = [ 3; 1; 2 ]
let result =
  List.length l + List.fold_left ( + ) 0 l + List.nth (List.map (fun x -> x * 2) l) 1
  + List.hd (List.rev (l @ [ 4 ])) + fst (1, 2) + snd (3, 4) + abs (-5) + min 1 2 + max 3 4
  + (if List.exists (fun x -> x > 2) l && List.for_all (fun x -> x > 0) l then 1 else 0)
  + List.length (List.filter (fun x -> x mod 2 = 1) l) + List.find (fun x -> x < 3) l
  + List.assoc 2 [ (1, 10); (2, 20) ] + Option.get (Option.map succ (Some 1))
  + List.fold_right (fun x acc -> x - acc) l 0
