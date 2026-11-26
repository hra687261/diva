(* pattern matching *)
type shape = Square of int | Rect of int * int | Empty
let area = function Square n -> n * n | Rect (w, h) -> w * h | Empty -> 0
let small = function 0 | 1 | 2 -> true | _ -> false
let first_pos = function x :: _ when x > 0 -> Some x | _ :: y :: _ when y > 0 -> Some y | _ -> None
let get_or d = function Some x -> x | None -> d
let rec zip l1 l2 = match (l1, l2) with x :: xs, y :: ys -> (x, y) :: zip xs ys | _, _ -> []
let result =
  area (Rect (3, 4)) + area (Square 5) + area Empty
  + (if small 1 && not (small 5) then 1 else 0)
  + get_or 0 (first_pos [ 0; 5 ]) + get_or 7 (first_pos [ -1; -2 ])
  + (match zip [ 1; 2 ] [ 3 ] with [ (x, y) ] -> x * 10 + y | _ -> 0)
