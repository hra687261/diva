(* `/` and `mod` round towards zero, as in OCaml *)
let result = (-7 / 2) + (7 / -2) * 10 + (-7 mod 2) * 100 + (7 mod -2) * 1000
