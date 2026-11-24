(* Showcase 1 of the plan. The branch `then 0` is dead: `acc` is a sum of squares.
   The analysis infers `acc >= 0` (`diva hints`), and `diva prove --infer` turns the
   hints into the contract of `sumsq`, which Lean then checks. *)
let rec sumsq n acc =
  if n = 0 then acc
  else
    let acc = acc + n * n in
    if acc < 0 then 0
    else sumsq (n - 1) acc

;; sumsq 10 0
