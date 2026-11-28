(* Lists that can't be `[]`, and an exhaustive `match`. *)

(* `l` has three elements: `List.hd` can't raise `Failure` *)
let l = [ 3; 1; 2 ]
let a = List.hd l

(* a non-empty list stays non-empty after `::` *)
let second l = match l with _ :: x :: _ -> x | _ -> 0
let b = second (0 :: l)

(* the `match` matches every list: its last case `[]` isn't tested, so no
   `Match_failure` is possible. But the analysis doesn't know that the recursive call
   gets a non-empty list: `Failure` is reported. *)
let rec last = function [ x ] -> x | _ :: l -> last l | [] -> failwith "last"
let c = last l

(* the lengths of lists: `l2` has 2 or 3 elements, so `_ :: y :: _` matches. Its
   elements one by one are lost in the join, its lengths are not *)
let l2 = if c > 0 then [ 1; 2 ] else [ 1; 2; 3 ]
let d = match l2 with _ :: y :: _ -> y | _ -> failwith "short"

(* `List.length` gives the lengths of the lists: `List.length l2 - 1` is 1 or 2 *)
let e = 10 / (List.length l2 - 1)
