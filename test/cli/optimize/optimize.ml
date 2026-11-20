(* What `diva opt` does with the facts of the analysis. *)

let width = 8
let height = width * 2 + 4        (* constant folding: 20 *)
let area = width * height         (* constant propagation: 160 *)

let debug = false
let scale x =
  if debug then x * 1000          (* `debug` is known: this branch is removed *)
  else if x < 0 then 0
  else x * 1 + 0                  (* `x` is an integer here: `* 1` and `+ 0` disappear *)

let clamp x =
  if x < 0 then 0
  else if x < 0 then 1            (* dead: `x < 0` is false here *)
  else (assert (x >= 0); x)       (* proved, so `assert` becomes `()` *)
;;
scale area + clamp 3
