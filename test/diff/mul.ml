(* overflow *)
(* a product that wraps around *)
let rec pow a n = if n = 0 then 1 else a * pow a (n - 1)
let result = pow 10 19
