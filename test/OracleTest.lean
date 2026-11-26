import Diva.Commands

open Diva Oracle AbsInt Lean

/-- The hints in `answer`, as `diva hints` prints them, or the line `error: ...` that
    says why `answer` is rejected. The program has the hint keys `n#1` and `$f#0`. -/
def hintsIn (answer : String) : List String :=
  match parseFacts (A := Itv) ["n#1", "$f#0"] answer with
  | .ok H => H.map fun (x, a) => s!"{x} : {a}"
  | .error msg => [s!"error: {msg}"]

/-- An answer with the facts `fs`: each fact is the name it is about, and the formula. -/
def facts (fs : List (String × String)) : String :=
  let fs := fs.map fun (about, holds) => json% {"about": $about, "holds": $holds}
  (json% {"facts": $(fs.toArray)}).compress

/-- An answer with one fact about `$f#0`. -/
def fact (holds : String) : String := facts [("$f#0", holds)]

-- facts: comparisons of `v` with an integer, joined by `&&`
#guard hintsIn (fact "-5 <= v && v <= -4") == ["$f#0 : [-5, -4]"]
#guard hintsIn (fact "0 < v") == ["$f#0 : [1, +∞]"]

-- `<>` keeps all the integers: the domain may not have a value for "all but 3"
#guard hintsIn (fact "v <> 3") == ["$f#0 : [-∞, +∞]"]

-- anything else is rejected
#guard hintsIn "$f#0 : [-5, -4]" == ["error: the answer is not only JSON"]
#guard hintsIn (json% {"hints": []}).compress == ["error: the answer has no list `facts`"]
#guard hintsIn (facts [("g", "v = 3")]) ==
  ["error: `g` is not a parameter or a function result (`$f`) of the program"]
#guard hintsIn (fact "v = n") == ["error: `v = n`: a fact compares `v` with an integer"]
#guard hintsIn (fact "v <= ") == ["error: `v <= ` is not a formula"]
#guard hintsIn (facts [("n#1", "v = 1"), ("n#1", "v = 2")]) ==
  ["error: two facts are about the same name"]

-- The rounds are tested in `test/cli/oracle`. Two more cases:

/-- `f 0` is -5. The inference finds that `f` returns a value in `[-5, +∞]`. -/
def src := "let rec f n = if n >= 100 then n - 105 else f (n + 2) in 10 / f 0"

/-- An oracle that always gives `answer`, without IO. -/
def always (answer : String) : String → Id String := fun _ => answer

-- no fact: the oracle is asked once
#guard (Commands.checkOracle (always (facts [])) 3 src).out ==
  ["round 1: the oracle proposes", "  nothing", "rejected",
   "`10 / f 0`: possible division by zero (divisor: [-5, +∞])"]
-- a safe program: the oracle isn't asked
#guard (Commands.checkOracle (always "") 3 "10 / 2").out == ["no runtime error is possible"]

-- with the source, the question shows it, and the places where the program may fail
-- have their positions in it
#guard
  let src := "let rec f n = if n >= 100 then n - 105 else f (n + 2)\n;; 10 / f 0"
  match parseLoc src with
  | .ok ⟨e, l⟩ =>
    let lines := (prompt ([] : AEnv Itv) e [] none (some ⟨"f.ml", src, l⟩)).splitOn "\n"
    lines.contains "  ;; 10 / f 0" &&
      lines.contains "  f.ml:2:3-11: `10 / f 0`: possible division by zero (divisor: [-5, +∞])"
  | .error _ => false
