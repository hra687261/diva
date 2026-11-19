import Diva.Parser
import Diva.AbsInt.ItvDomain
import Diva.AbsInt.Aeval
import Diva.AbsInt.Infer
import Diva.AbsInt.MayFail

open Diva Diva.AbsInt

private def itv (lo hi : Int) : Itv := .range (.fin lo) (.fin hi)

/-- Analyse `s` with `x ∈ [0, 10]`. -/
private def analyse (s : String) : Option String :=
  (Diva.parse s).toOption.map fun e =>
    toString (aeval [] ([("x", AVal.ofInt (itv 0 10))] : AEnv Itv) e)

#guard analyse "x + 1"                         = some "[1, 11]"
#guard analyse "2 * x - 3"                     = some "[-3, 17]"
#guard analyse "let y = x * x in y + 1"        = some "[1, 101]"
#guard analyse "x / 2"                         = some "[0, 5]"
#guard analyse "x mod 3"                       = some "[0, 2]"
#guard analyse "if x < 5 then 0 else 100"      = some "[0, 100]"
#guard analyse "y"                             = some "⊤"         -- unknown variable
#guard analyse "let x = 7 in x"                = some "7"         -- shadowing
#guard analyse "(fun y -> y) 3"                = some "⊤"         -- no precondition on `y`

-- branch refinement: `x < 5` narrows `x` in each branch
#guard analyse "if x < 5 then x else 0"          = some "[0, 4]" -- join of both branches
#guard analyse "if x < 5 then 0 else x"          = some "[0, 10]"
#guard analyse "if x < 5 then 0 else x - 5"      = some "[0, 5]"
#guard analyse "if 3 <= x then x else 3"         = some "[3, 10]"
#guard analyse "if x > 7 then x else 7"          = some "[7, 10]"
#guard analyse "if x >= 7 then 0 else x"         = some "[0, 6]"
#guard analyse "if x < 20 then x else 100"       = some "[0, 10]"  -- else is dead
#guard analyse "if x > 10 then 1 else 2"         = some "2"        -- then is dead
#guard analyse "if x + 1 < 5 then x else 0"      = some "[0, 10]"  -- only atoms narrow
#guard analyse "let y = x in if y < x then y else 0" = some "[0, 9]"

-- other kinds of values
#guard analyse "true"                            = some "true"
#guard analyse "()"                              = some "()"
#guard analyse "[1; 2]"                          = some "non-empty list of [1, 2]"
#guard analyse "fun y -> y"                      = some "fun ⊤ -> ⊤"
#guard analyse "let rec f y = y in f"            = some "fun ⊤ -> ⊤"
#guard analyse "E 1"                             = some "exn"
#guard analyse "x < 5"                           = some "bool"
#guard analyse "x < 20"                          = some "true"
#guard analyse "x = 3"                           = some "bool"
#guard analyse "if x < 5 then true else ()"      = some "true | ()"
#guard analyse "raise E"                         = some "⊥"        -- never gives a value
#guard analyse "if x > 20 then raise E else 1"   = some "1"
#guard analyse "if 1 then 2 else 3"              = some "⊥"        -- not a boolean: an error
#guard analyse "let b = x < 20 in if b then 1 else 2" = some "1"   -- `b` is surely true

-- `=` and `<>`: a boolean, and `=` narrows both sides in its `then` branch
#guard analyse "x = 20"                          = some "false"
#guard analyse "x <> 20"                         = some "true"
#guard analyse "true = true"                     = some "true"
#guard analyse "() = ()"                         = some "true"
#guard analyse "if x = 3 then x else 0"          = some "[0, 3]"
#guard analyse "if x = 3 then x + 1 else 4"      = some "4"
#guard analyse "if x <> 3 then 0 else x"         = some "[0, 3]"
#guard analyse "if x = 20 then 1 else 2"         = some "2"        -- then is dead
#guard analyse "let y = x in if y = 3 then y else 3" = some "3"

/-- Analyse `s` with `x ∈ [0, 10]` and the hints `H`. -/
private def analyseH (H : List (String × Itv)) (s : String) : Option String :=
  (Diva.parse s).toOption.map fun e =>
    toString (aeval (H.map fun (k, i) => (k, Flat.ofInt i))
      ([("x", AVal.ofInt (itv 0 10))] : AEnv Itv) e)

-- functions: a summary from the parameter's precondition
#guard analyseH [("y#0", itv 0 10)] "fun y -> y + 1"           = some "fun [0, 10] -> [1, 11]"
#guard analyseH [("y#0", itv 0 10)] "(fun y -> y + 1) x"       = some "[1, 11]"
#guard analyseH [("y#0", itv 0 10)] "let f = fun y -> y + 1 in f (f x)" = some "⊤"  -- `f x` ∉ [0, 10]
#guard analyseH [("y#0", itv 0 10)] "let f = fun y -> y + 1 in f 20"    = some "⊤"  -- 20 ∉ [0, 10]
#guard analyseH [("y#0", itv 0 20)] "let f = fun y -> y / 2 in f (f x)" = some "[0, 10]"

-- recursive functions: the claimed result (`$f`) is checked against the body
private def countdown := "let rec f y = if y <= 0 then 0 else f (y - 1) in f x"
#guard analyseH [("y#1", itv 0 10), ("$f#0", itv 0 0)] countdown  = some "0"
#guard analyseH [("y#1", itv 0 10), ("$f#0", itv 5 5)] countdown  = some "⊤"  -- wrong claim: dropped
#guard analyseH [("y#1", itv 0 10)] countdown                    = some "⊤"  -- no claim

/-! ## Inferred hints -/

private def σx : AEnv Itv := [("x", AVal.ofInt (itv 0 10))]

/-- The hints inferred for `s`, with `x ∈ [0, 10]`. -/
private def hintsOf (s : String) : Option String :=
  (Diva.parse s).toOption.map fun e =>
    toString ((inferHints σx e).map fun (k, a) => s!"{k}: {a}")

/-- Analyse `s` with the hints inferred for it. -/
private def analyseI (s : String) : Option String :=
  (Diva.parse s).toOption.map fun e => toString (aeval (inferHints σx e) σx e)

-- preconditions: the join of the arguments
#guard hintsOf "let f = fun y -> y + 1 in f x"          = some "[y#0: [0, 10]]"
#guard analyseI "let f = fun y -> y + 1 in f x"         = some "[1, 11]"
#guard hintsOf "let f = fun y -> y / 2 in f (f x)"      = some "[y#0: [0, 10]]"
#guard analyseI "let f = fun y -> y / 2 in f (f x)"     = some "[0, 5]"
-- `y` must cover `y + 1`: widened to `+∞`
#guard hintsOf "let f = fun y -> y + 1 in f (f x)"      = some "[y#0: [0, +∞]]"
#guard analyseI "let f = fun y -> y + 1 in f (f x)"     = some "[1, +∞]"
-- a function reached through another variable
#guard analyseI "let g = fun y -> y in let h = g in h 3" = some "3"
-- a parameter that no call reaches: no hint (anything)
#guard hintsOf "fun y -> y"                             = some "[]"

-- recursive functions: the precondition covers the recursive calls too
#guard hintsOf countdown                                = some "[y#1: [0, 10], $f#0: 0]"
#guard analyseI countdown                               = some "0"
private def count := "let rec f y = if y <= 0 then 0 else 1 + f (y - 1) in f x"
#guard hintsOf count                                    = some "[y#1: [0, 10], $f#0: [0, +∞]]"
#guard analyseI count                                   = some "[0, +∞]"
-- never returns
#guard analyseI "let rec f y = f y in f x"              = some "⊥"
-- two parameters named `y` get a hint each
private def twoY := "let f = fun y -> y + 1 in let g = fun y -> if y then 1 else 2 in f 3 + g true"
#guard hintsOf twoY  = some "[y#0: 3, y#1: true]"
#guard analyseI twoY = some "5"

/-! ## Possible errors -/

/-- Whether `s` may fail, with `x ∈ [0, 10]`. -/
private def mayFailS (s : String) : Option Bool :=
  (Diva.parse s).toOption.map fun e => mayFail ([] : Hints Itv) σx e

#guard mayFailS "x + 1"                           = some false
#guard mayFailS "10 / x"                          = some true   -- `x` may be `0`
#guard mayFailS "10 / (x + 1)"                    = some false
#guard mayFailS "if x > 0 then 10 / x else 0"     = some false  -- `x` is narrowed
#guard mayFailS "if x < 5 then 10 / x else 0"     = some true
#guard mayFailS "x"                               = some false  -- bound
#guard mayFailS "y"                               = some true   -- unbound
#guard mayFailS "1 + true"                        = some true   -- type error
#guard mayFailS "x = 3"                           = some false
#guard mayFailS "x = true"                        = some true
#guard mayFailS "assert (x < 20)"                 = some false
#guard mayFailS "assert (x < 5)"                  = some true
#guard mayFailS "if 1 then 2 else 3"              = some true
#guard mayFailS "if x > 20 then 1 / 0 else 1"     = some false  -- dead branch
#guard mayFailS "let y = x - 1 in 10 / y"         = some true   -- `y` may be `0`
#guard mayFailS "x :: [1]"                        = some false
#guard mayFailS "x :: 1"                          = some true
#guard mayFailS "raise E"                         = some true
#guard mayFailS "let rec f y = f y in x"          = some false
#guard mayFailS "(fun y -> y) 1"                  = some false
-- with no hint, a parameter may be anything: `10 / y` may fail
#guard mayFailS "(fun y -> 10 / y) 1"             = some true

/-- Whether `s` may fail, with `x ∈ [0, 10]` and the hints `H`. -/
private def mayFailH (H : List (String × Itv)) (s : String) : Option Bool :=
  (Diva.parse s).toOption.map fun e => mayFail (H.map fun (k, i) => (k, Flat.ofInt i)) σx e

/-- Whether `s` may fail, with `x ∈ [0, 10]` and the hints inferred for it. -/
private def mayFailI (s : String) : Option Bool :=
  (Diva.parse s).toOption.map fun e => mayFail (inferHints σx e) σx e

-- calls: they fail only if the body may, for an argument in the precondition
#guard mayFailH [("y#0", itv 1 11)] "(fun y -> 10 / y) (x + 1)"           = some false
#guard mayFailH [("y#0", itv 1 10)] "(fun y -> 10 / y) x"                 = some true  -- `x` ∉ [1, 10]
#guard mayFailH [("y#0", itv 0 10)] "(fun y -> 10 / y) (x + 1)"           = some true  -- the body may fail
#guard mayFailH [("y#0", itv 1 10)] "let f = fun y -> 10 / y in f 3 + f 5" = some false
#guard mayFailS "1 2"                                                     = some true  -- not a function
-- recursive functions: the body is checked assuming the recursive calls don't fail
#guard mayFailH [("y#1", itv 0 10), ("$f#0", itv 0 0)] countdown = some false

private def divRec :=
  "let rec f y = if y <= 0 then 0 else (let z = 10 / y in f (y - 1)) in f x"
#guard mayFailH [("y#1", itv 0 10), ("$f#0", itv 0 0)] divRec    = some false

private def divDown :=
  "let rec f y = if y < 0 then 0 else (let z = 10 / y in f (y - 1)) in f x"
#guard mayFailH [("y#1", itv 0 10), ("$f#0", itv 0 0)] divDown   = some true
-- `y` may be `0` with inferred hints

#guard mayFailI countdown                                       = some false
#guard mayFailI "let f = fun y -> 10 / y in f (x + 1)"          = some false


/-! ## Curried functions -/

private def ab : List (String × Itv) := [("a#0", itv 0 10), ("b#1", itv 0 5)]

-- `fun a b -> e` gets one summary, with a precondition per parameter
#guard analyseH ab "fun a b -> a + b"                         = some "fun [0, 10] -> [0, 5] -> [0, 15]"
#guard analyseH ab "let f a b = a + b in f x 2"               = some "[0, 15]"

-- `f 1` gives the summary of the other parameter
#guard analyseH ab "let f a b = a + b in let g = f 1 in g 2"  = some "[0, 15]"
#guard mayFailH [("a#0", itv 0 10), ("b#1", itv 1 5)] "let f a b = a / b in f x 2" = some false
#guard mayFailH ab "let f a b = a / b in f x 2"               = some true   -- `b` may be `0`
#guard mayFailH ab "let f a b = a / b in f x"                 = some false  -- only builds a closure

-- with inferred hints: each argument is a claim on its own parameter
#guard hintsOf "let f a b = a + b in f x 2"                   = some "[a#0: [0, 10], b#1: 2]"
#guard analyseI "let f a b = a + b in f x 2"                  = some "[2, 12]"
#guard analyseI "let f a b c = a + b + c in f 1 2 3"          = some "6"
#guard mayFailI "let f a b c = a / (b + c) in f 1 2 3"        = some false

-- a recursive function of two parameters
private def countAcc := "let rec f n acc = if n <= 0 then acc else f (n - 1) (acc + 1) in f x 0"
#guard hintsOf countAcc  = some "[n#1: [0, 10], $f#0: [0, +∞], acc#2: [0, +∞]]"
#guard analyseI countAcc = some "[0, +∞]"
#guard mayFailI countAcc = some false
-- lists: described by their elements
#guard analyse "[]"                                   = some "list of ⊥"
#guard analyse "x :: [3]"                             = some "non-empty list of [0, 10]"
#guard analyse "if x < 5 then [1] else [2]"           = some "non-empty list of [1, 2]"
#guard analyse "match [x; 3] with [] -> 0 | h :: t -> h + 1" = some "[1, 11]"  -- never `[]`
#guard analyse "match [x] with [] -> [] | h :: t -> t"       = some "list of [0, 10]"
#guard analyse "match y with [] -> 0 | h :: t -> h"          = some "⊤"  -- `y` unknown
#guard analyse "match [] with [] -> 0 | h :: t -> h"         = some "0"  -- always `[]`
#guard analyse "match (if x < 5 then [] else [x]) with [] -> 0 | h :: t -> h" = some "[0, 10]"
-- the inference looks inside `match`
#guard analyseI "let f = fun y -> y + 1 in match [x] with [] -> 0 | h :: t -> f h"
  = some "[1, 11]"
-- `match` fails only through a branch that can be taken, or if it is not on a list
#guard mayFailS "match [x] with [] -> 1 / 0 | h :: t -> h"       = some false  -- never `[]`
#guard mayFailS "match [x] with [] -> 0 | h :: t -> 10 / h"      = some true   -- `h` may be `0`
#guard mayFailS "match [x + 1] with [] -> 0 | h :: t -> 10 / h"  = some false
#guard mayFailS "match [] with [] -> 0 | h :: t -> 1 / 0"        = some false  -- always `[]`
#guard mayFailS "match 1 with [] -> 0 | h :: t -> h"             = some true   -- not a list

/-! ## Safety, checked by the kernel -/

-- `safe` turns the checker's answer into a theorem about every run of the program
example {μ μ' : Store} {k : Err} :
    ¬ Eval [] μ (.binop .div (.int 10) (.binop .add (.int 1) (.int 1))) (.err k) μ' :=
  safe (H := ([] : Hints Itv)) (by decide)
