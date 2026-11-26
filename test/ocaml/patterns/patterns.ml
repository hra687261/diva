(* Tuples, `option`, variants, nested patterns, `when` and or-patterns. *)

type shape = Square of int | Rect of int * int | Empty

let area s = match s with
  | Square n -> n * n
  | Rect (w, h) -> w * h
  | Empty -> 0

(* a tuple, built and taken apart *)
let swap (a, b) = (b, a)
let sum_pair p = let (a, b) = p in a + b

(* `option`, and a nested pattern *)
let first_pos l = match l with
  | x :: _ when x > 0 -> Some x
  | _ :: y :: _ when y > 0 -> Some y
  | _ -> None

let get_or d o = match o with Some x -> x | None -> d

(* an or-pattern, and constants *)
let small n = match n with 0 | 1 | 2 -> true | _ -> false

let rec zip l1 l2 = match l1, l2 with
  | x :: xs, y :: ys -> (x, y) :: zip xs ys
  | _, _ -> []

let () =
  let (a, b) = swap (1, 2) in
  print_int (area (Rect (3, 4)) + area (Square 5) + area Empty + a + b + sum_pair (10, 20));
  print_int (get_or 0 (first_pos [ 0; 5 ]) + get_or 7 (first_pos [ -1; -2 ]));
  print_int (if small 1 && not (small 5) then 1 else 0);
  match zip [ 1; 2 ] [ 3 ] with [ (x, y) ] -> print_int (x + y) | _ -> ()
