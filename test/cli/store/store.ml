(* Arrays and refs. The analysis knows the contents of each allocation site (the hints
   `!0`, `!1`, ...), and the length of each array (`!1.length`). It finds the access
   `a.(10)` out of bounds. Without the line `let y = a.(10)`, the program has no error,
   but this analysis isn't proved yet: `check` says so, and `cert` gives no certificate. *)

let sum_to n =
  let s = ref 0 in
  for i = 1 to n do
    s := !s + i
  done;
  !s

let a = Array.make 10 0
let _ = for i = 0 to 9 do a.(i) <- sum_to i done
let x = a.(3) + a.(9)
let y = a.(10)
