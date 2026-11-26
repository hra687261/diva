(* An ordinary OCaml file: type annotations, `function`, `let () =`, output,
   exceptions, loops and refs. *)

exception Empty

let rec length : int list -> int = function
  | [] -> 0
  | _ :: t -> 1 + length t

let head l = match l with [] -> raise Empty | x :: _ -> x

let safe_head l = try head l with Empty -> 0

let sum_to n =
  let s = ref 0 in
  for i = 1 to n do
    s := !s + i
  done;
  !s

let rec fact (n : int) =
  if n <= 1 then 1 else n * fact (n - 1)
(*@ requires n >= 0 *)

let () =
  let l = [ 1; 2; 3 ] in
  print_int (length l + safe_head [] + sum_to 4 + fact 5);
  print_newline ();
  if Char.code 'a' <> 97 then failwith "chars"
