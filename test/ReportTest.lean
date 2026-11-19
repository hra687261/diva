import Diva.Parser
import Diva.AbsInt.ItvDomain
import Diva.Report

open Diva Diva.AbsInt

/-- The report for the program `s`, with inferred hints. -/
private def check (s : String) : Option (List String) :=
  (Diva.parse s).toOption.map (Report.report ([] : AEnv Itv))

#guard check "1 + 2" = some ["no runtime error is possible"]
#guard check "let f y = 10 / y in f 3" = some ["no runtime error is possible"]

-- division by zero, inside the function, and at each call
#guard check "let f y = 10 / y in f 0 + f 3" = some [
  "`(10 / y)`: possible division by zero (divisor: [0, 3])",
  "`(f 0)`: the function called may fail",
  "`(f 3)`: the function called may fail"]

-- type errors
#guard check "1 + true" = some ["`(1 + true)`: the operands may not be integers (1 and true)"]
#guard check "1 :: 2" = some ["`(1 :: 2)`: the tail may not be a list (2)"]
#guard check "if 1 then 2 else 3" = some ["`1` may not be a boolean (1)"]
#guard check "match 1 with [] -> 0 | h :: t -> h" =
  some ["`(match 1 with [] -> 0 | h :: t -> h)`: may not match a list (1)"]
#guard check "y" = some ["`y` may be unbound"]

-- `assert`
#guard check "assert (1 < 2)" = some ["no runtime error is possible"]
-- one summary for all calls: `y` is in `[3, 7]`, so `f 3` may fail too
#guard check "let f y = assert (y < 5) in f 3; f 7" = some [
  "`(assert (y < 5))` may fail",
  "`(f 3)`: the function called may fail",
  "`(f 7)`: the function called may fail"]

-- dead branches are not reported
#guard check "if 1 < 2 then 0 else 1 / 0" = some ["no runtime error is possible"]
#guard check "match [1] with [] -> 1 / 0 | h :: t -> h" = some ["no runtime error is possible"]

-- a call the inference can't follow: the function is a parameter
#guard check "let g f = f 1 in g (fun x -> x + 1)" = some [
  "`(f 1)`: calls a function the analysis knows nothing about",
  "`(x + 1)`: the operands may not be integers (⊤ and 1)",
  "`(g (fun x -> (x + 1)))`: the function called may fail"]
-- TODO: add type-checking and low-effort form of type inference/unification

-- not analysed yet
#guard check "raise E" = some ["`(raise E)`: not analysed yet, so it may fail"]
