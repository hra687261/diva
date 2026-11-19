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

-- TODO: calls are not optimized
#guard optimized "let f x = x * x in f 3 + 1"   = some "(let f = (fun x -> (x * x)) in ((f 3) + 1))"
#guard optimized "let f y = y + 1 in f (2 + 3)" = some "(let f = (fun y -> (y + 1)) in (f 5))"

-- something that may fail is not optimized
#guard optimized "1 / 0 + 2"                    = some "((1 / 0) + 2)"

-- the results don't change
#guard sameResult "let rec range a b = if a > b then [] else a :: range (a + 1) b in range 1 4"
#guard sameResult "let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact (2 + 3)"
#guard sameResult "1 / 0 + 2"
