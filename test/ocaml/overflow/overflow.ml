(* `diva ocaml` checks that each `+`, `-`, `*` and `/` fits in the bits of its type:
   63 for `int`, 32 for `Int32.t`, 64 for `Int64.t`. Lean proves `sum`: its contract
   bounds `n`. `next32 Int32.max_int` overflows: in OCaml, it wraps around to
   `Int32.min_int`. In DIVA, the check fails. *)

let rec sum n = if n <= 0 then 0 else n + sum (n - 1)
(*@ r = sum n
    requires 0 <= n && n <= 1000
    ensures 0 <= r && r <= 1000 * n *)

let next32 (x : int32) = Int32.add x 1l

;; sum 10 + Int32.to_int (next32 Int32.max_int)
