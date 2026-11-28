(* The functions of OCaml's standard library that [diva ocaml] knows, written in OCaml
   (untrusted).

   The frontend translates this file with the program, and adds the functions that the
   program uses before it. Each one behaves as the function of the same name in OCaml
   5.4's standard library: the same results, the same exceptions, and its arguments
   computed in the same order. Most are copied from it.

   [[@diva.unchecked]] marks an operation whose result can't overflow, so it gets no
   overflow check: a count of the elements of a list, which has fewer than [max_int]
   elements.

   [[@diva.inline]] marks a function that takes a function [f] as an argument. Its code
   is copied at each call that gives all its arguments. In the copy, [f] is the function
   given by the call, which DIVA's analysis knows. Without the copy, the analysis knows
   nothing about [f]: the hint of a parameter doesn't describe a function. *)

let fst (a, _) = a
let snd (_, b) = b
let abs x = if x >= 0 then x else -x
let min a b = if a <= b then a else b
let max a b = if a >= b then a else b
let succ n = n + 1
let pred n = n - 1

module List = struct
  let hd = function [] -> failwith "hd" | a :: _ -> a
  let tl = function [] -> failwith "tl" | _ :: l -> l

  let rec nth_aux l n =
    match l with
    | [] -> failwith "nth"
    | a :: l -> if n = 0 then a else nth_aux l ((n - 1) [@diva.unchecked])

  let nth l n = if n < 0 then invalid_arg "List.nth" else nth_aux l n
  let rec append l1 l2 = match l1 with [] -> l2 | a :: l -> a :: append l l2

  let rec rev_append l1 l2 =
    match l1 with [] -> l2 | a :: l -> rev_append l (a :: l2)

  let rev l = rev_append l []

  let[@diva.inline] map f l =
    let rec map = function
      | [] -> []
      | a :: l ->
          let r = f a in
          r :: map l
    in
    map l

  let[@diva.inline] iter f l =
    let rec iter = function
      | [] -> ()
      | a :: l ->
          f a;
          iter l
    in
    iter l

  let[@diva.inline] fold_left f accu l =
    let rec fold_left accu l =
      match l with [] -> accu | a :: l -> fold_left (f accu a) l
    in
    fold_left accu l

  let[@diva.inline] fold_right f l accu =
    let rec fold_right l =
      match l with [] -> accu | a :: l -> f a (fold_right l)
    in
    fold_right l

  let[@diva.inline] exists p l =
    let rec exists = function [] -> false | a :: l -> p a || exists l in
    exists l

  let[@diva.inline] for_all p l =
    let rec for_all = function [] -> true | a :: l -> p a && for_all l in
    for_all l

  let rec mem x = function [] -> false | a :: l -> a = x || mem x l

  let[@diva.inline] filter p l =
    let rec filter = function
      | [] -> []
      | x :: l -> if p x then x :: filter l else filter l
    in
    filter l

  let[@diva.inline] find p l =
    let rec find = function
      | [] -> raise Not_found
      | x :: l -> if p x then x else find l
    in
    find l

  let rec assoc x = function
    | [] -> raise Not_found
    | (a, b) :: l -> if a = x then b else assoc x l
end

let ( @ ) l1 l2 = List.append l1 l2

module Option = struct
  let get = function Some v -> v | None -> invalid_arg "option is None"
  let is_some = function None -> false | Some _ -> true
  let is_none = function None -> true | Some _ -> false
  let[@diva.inline] map f o = match o with None -> None | Some v -> Some (f v)
end
