import Diva.Parser
import Diva.AbsInt.ItvDomain
import Diva.Report

open Diva Diva.AbsInt

/-- The report for the program `s`, with inferred hints. -/
private def check (s : String) : Option (List String) :=
  (Diva.parse s).toOption.map (Report.report ([] : AEnv Itv))

#guard check "1 + 2" = some ["no runtime error is possible"]
#guard check "let f y = 10 / y in f 3" = some ["no runtime error is possible"]

-- division by zero. The analysis that isn't proved yet analyses a copy of `f` at each
-- call (`Inline.expand`): only the copy for `f 0` divides by zero
#guard check "let f y = 10 / y in f 0 + f 3" = some [
  "`(10 / y)`: possible division by zero (divisor: 0)"]
-- a recursive function isn't copied: one summary for all its calls, so `f 3` is
-- reported too
#guard check "let rec f y = 10 / y in f 3 + f 0" = some [
  "`(10 / y)`: possible division by zero (divisor: [0, 3])",
  "`(f 3)`: the function called may fail",
  "`(f 0)`: the function called may fail"]

-- type errors
#guard check "1 + true" = some ["`(1 + true)`: the operands may not be integers (1 and true)"]
#guard check "1 :: 2" = some ["`(1 :: 2)`: the tail may not be a list (2)"]
#guard check "if 1 then 2 else 3" = some ["`1` may not be a boolean (1)"]
#guard check "match 1 with [] -> 0 | h :: t -> h" =
  some ["`(match 1 with [] -> 0 | h :: t -> h)`: may not match a list (1)"]
#guard check "y" = some ["`y` may be unbound"]

-- `assert`
#guard check "assert (1 < 2)" = some ["no runtime error is possible"]
-- each call has its copy: only the one for `f 7` fails
#guard check "let f y = assert (y < 5) in f 3; f 7" = some ["`(assert (y < 5))` may fail"]

-- dead branches are not reported
#guard check "if 1 < 2 then 0 else 1 / 0" = some ["no runtime error is possible"]
#guard check "match [1] with [] -> 1 / 0 | h :: t -> h" = some ["no runtime error is possible"]

-- a function given as an argument: in the copy of `g`, `f` is that function
#guard check "let g f = f 1 in g (fun x -> x + 1)" = some [Report.unprovedSafe]
-- without a copy, the analysis knows nothing about a function given as an argument
#guard check "let rec g f = f 1 in g (fun x -> x + 1)" = some [
  "`(f 1)`: calls a function the analysis knows nothing about",
  "`(x + 1)`: the operands may not be integers (⊤ and 1)",
  "`(g (fun x -> (x + 1)))`: the function called may fail",
  "`(g (fun x -> (x + 1)))`: may raise an exception that isn't caught (ctor)"]

-- exceptions (not proved yet): an exception that isn't caught is reported at its
-- top-level item
#guard check "raise E" = some ["`(raise E)`: may raise an exception that isn't caught (E)"]
#guard check "try raise (E 1) with E x -> x + 1" = some [Report.unprovedSafe]
#guard check "let f x = if x < 0 then raise Neg else x in try f 1 with Neg -> 0" =
  some [Report.unprovedSafe]
-- each call has its copy: `f 1` doesn't raise `Neg`
#guard check "let f x = if x < 0 then raise Neg else x in f 1; try f (0 - 1) with Neg -> 0" =
  some [Report.unprovedSafe]
-- the handler gets the argument of the exception
#guard check "try raise (E 0) with E x -> 10 / x" =
  some ["`(10 / x)`: possible division by zero (divisor: 0)"]

-- the elements of lists (not proved yet): the hint of `l` is `list of [1, 3]`
#guard check "let rec sum l = match l with [] -> 0 | x :: xs -> x + sum xs in sum [1; 2; 3]" =
  some [Report.unprovedSafe]
#guard check "let rec sum l = match l with [] -> 0 | x :: xs -> 10 / x + sum xs in sum [1; 0]" =
  some ["`(10 / x)`: possible division by zero (divisor: [0, 1])",
    "`(sum (1 :: (0 :: [])))`: the function called may fail"]
