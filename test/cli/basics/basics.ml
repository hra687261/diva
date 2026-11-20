(* Basics: top-level definitions, recursion, lists, higher-order functions.
   `diva check` can't verify it yet: the analysis doesn't know that the parameter
   `l` of the recursive functions is always a list. *)

let rec fact n = if n <= 1 then 1 else n * fact (n - 1)

let rec length l = match l with [] -> 0 | _ :: t -> 1 + length t

let rec map f l = match l with [] -> [] | x :: xs -> f x :: map f xs

let rec sum l = match l with [] -> 0 | x :: xs -> x + sum xs

let rec range a b = if a > b then [] else a :: range (a + 1) b

let squares = map (fun x -> x * x) (range 1 5)
let total = sum squares
let n = length squares
let ok = total = 55 && not (n <> 5)
let f10 = fact 10
;;
assert ok;
f10
