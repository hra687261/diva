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
