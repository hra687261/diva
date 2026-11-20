import Diva.Parser
import Diva.Interp
import Diva.AbsInt.ItvDomain
import Diva.Opt
import Diva.Report

open Diva Diva.AbsInt

/-- `s` optimised, printed without the `#n` suffixes of names. -/
private def optimized (s : String) : Option String :=
  (Diva.parse s).toOption.map fun e =>
    Report.clean (toString (Opt.optimize ([] : AEnv Itv) e))

/-- `s` and its optimised version give the same result (closures aside). -/
private def sameResult (s : String) : Bool :=
  match Diva.parse s with
  | .ok e =>
    let run (e : Expr) : String :=
      match eval 10000 [] [] e with
      | .ok v _ => toString v
      | .err k _ => ppErr k
      | .outOfFuel => "out of fuel"
    run e == run (Opt.optimize ([] : AEnv Itv) e)
  | .error _ => false

-- constant folding
#guard optimized "2 * 3 + 1"                              = some "7"
#guard optimized "let x = 8 in let y = x * 2 + 4 in y"    = some "20"
#guard optimized "let x = 3 < 5 in if x then 1 else 2"    = some "1"
#guard optimized "if 1 < 2 then 3 else 4"                 = some "3"

-- inside a function the parameter is `⊤`: only the parts that don't depend on it fold
#guard optimized "let f x = let y = x + 1 in y + 2 * 3 in f" =
  some "(let f = (fun x -> (let y = (x + 1) in (y + 6))) in f)"

-- a branch knows its condition: in the `then` branch `x < 3`, so `x < 5`
#guard optimized "fun x -> if x < 3 then (if x < 5 then 1 else 2) else 0" =
  some "(fun x -> (if (x < 3) then 1 else 0))"

-- dead branches: a condition that is certainly `true` keeps only the `then` branch
#guard optimized "fun y -> let x = 2 in if x < 3 then y + 1 else y" =
  some "(fun y -> (let x = 2 in (y + 1)))"
#guard optimized "fun y -> let x = 2 in if x > 3 then y + 1 else y" =
  some "(fun y -> (let x = 2 in y))"

-- in the `then` branch `x < 3`, so `x < 5` is certainly `true`
#guard optimized "fun x -> if x < 3 then (if x < 5 then x + 1 else 0) else 0" =
  some "(fun x -> (if (x < 3) then (x + 1) else 0))"

-- a condition that may fail is kept
#guard optimized "fun y -> if 1 / 0 < 3 then y else 0" =
  some "(fun y -> (if ((1 / 0) < 3) then y else 0))"

-- proved assertions become `()`
#guard optimized "fun x -> if x < 3 then (assert (x < 5); x) else 0" =
  some "(fun x -> (if (x < 3) then (let _ = () in x) else 0))"
-- TODO: remove the let-binding `let _ = () in ...`

-- an assertion that may not hold is kept
#guard optimized "fun x -> assert (x < 5); x" =
  some "(fun x -> (let _ = (assert (x < 5)) in x))"

-- identities: `x + 0`, `x * 1`, `0 + x`, ... become `x` when `x` is certainly an integer
#guard optimized "fun x -> if x < 3 then x * 1 + 0 else 0" =
  some "(fun x -> (if (x < 3) then x else 0))"
#guard optimized "fun x -> if x < 3 then 0 + (1 * x) / 1 else 0" =
  some "(fun x -> (if (x < 3) then x else 0))"
#guard optimized "fun x -> let z = 0 in if x < 3 then x - z else 0" =
  some "(fun x -> (let z = 0 in (if (x < 3) then x else 0)))"
-- `x` may not be an integer: `x + 0` may fail, and is kept
#guard optimized "fun x -> x + 0" = some "(fun x -> (x + 0))"

-- TODO: calls are not optimized
#guard optimized "let f x = x * x in f 3 + 1"   = some "(let f = (fun x -> (x * x)) in ((f 3) + 1))"
#guard optimized "let f y = y + 1 in f (2 + 3)" = some "(let f = (fun y -> (y + 1)) in (f 5))"

-- something that may fail is not optimized
#guard optimized "1 / 0 + 2"                    = some "((1 / 0) + 2)"

-- the results don't change
#guard sameResult "let rec range a b = if a > b then [] else a :: range (a + 1) b in range 1 4"
#guard sameResult "let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact (2 + 3)"
#guard sameResult "1 / 0 + 2"
#guard sameResult "let f y = let x = 2 in if x < 3 then y + 1 else y in f 4"
#guard sameResult "let f x = if x < 3 then (assert (x < 5); x) else 0 in f 1"
#guard sameResult "let f x = if x < 3 then 0 + (1 * x) / 1 else 0 in f 2"
#guard sameResult "let f x = x + 0 in f true"
