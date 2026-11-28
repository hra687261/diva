(* Array literals: `[|a; b; c|]` is an array of 3 copies of `a`, where `b` and `c` are
   then written. The analysis knows its length, and the values of its elements. *)

let a = [| 4; 2; 8 |]

(* the indices are in bounds, and no element is 0 *)
let b = 100 / a.(0) + 100 / a.(2)

let sum t =
  let s = ref 0 in
  for i = 0 to Array.length t - 1 do
    s := !s + t.(i)
  done;
  !s

let empty = [||]
let c = Array.length empty
;;

b + sum a + c
