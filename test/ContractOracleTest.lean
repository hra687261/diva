import Diva.Commands

open Diva ContractOracle Lean

/-- An answer with the program `src`, one line per string. -/
def answer (src : String) : String :=
  (json% {"program": $((src.splitOn "\n").toArray)}).compress

/-- The items of `src`. -/
def items (src : String) : List Item := (parseItems src).toOption.getD []

/-- `c` calls `b`, which calls `a`. Only `c` has a contract. -/
def src := "let a x = x\nlet b x = a x\nlet c x = b x\n(*@ ensures result = x *)\nlet d x = x"

-- the functions that need a contract: those called by `c`, and the ones they call
#guard calledWithoutContract (items src) == ["b", "a"]

-- an answer that changes the code, or a contract of the user, is rejected
#guard changes (items src) (items "let a x = x\nlet b x = a x\nlet c x = b x\n(*@ ensures result = x *)\nlet d x = 0") ==
  some "it changes the code"
#guard changes (items src) (items "let a x = x\nlet b x = a x\nlet c x = b x\n(*@ ensures result >= x *)\nlet d x = x") ==
  some "it changes the contract of `c`"
#guard changes (items src) (items "let a x = x\n(*@ ensures result = x *)\nlet b x = a x\nlet c x = b x\n(*@ ensures result = x *)\nlet d x = x") ==
  none

/-- A mock Lean, without IO: it accepts every file. -/
def lean (_ : String) : Id (Option String) := none

-- an answer that Lean accepts: the round, then the program
#guard (Commands.specOracle (fun _ => (answer src : Id String)) lean 1 src).out ==
  ["round 1: the oracle proposes", "accepted", "", src]
-- an answer that isn't only JSON is rejected, and the oracle is asked again
#guard (Commands.specOracle (fun _ => (src : Id String)) lean 1 src).out ==
  ["round 1: the answer of the oracle isn't in the format: the answer is not only JSON"]
-- no contract: the oracle writes the contracts of all the functions, with a warning
#guard toSpecify (items "let f x = x\nlet g x = f x\n;; g 1") == ["f", "g"]
#guard (Commands.specOracle (fun _ => (answer "let f x = x\n(*@ ensures result = x *)" : Id String))
    lean 1 "let f x = x").out ==
  ["round 1: the oracle proposes", "  f: (*@ ensures (result = x) *)", "accepted", "",
   "warning: the oracle wrote all the contracts. Read them to know what is proved.", "",
   "let f x = x\n(*@ ensures result = x *)"]
#guard (Commands.specOracle (fun _ => ("" : Id String)) lean 1 "1 + 2").err ==
  ["the program has no function"]

-- a local name with the name of a function isn't a call of that function
#guard calledWithoutContract
  (items "let a x = x\nlet c x = let a = 3 in a + x\n(*@ ensures result = x *)") == []
#guard calledWithoutContract
  (items "let a x = x\nlet c x = (fun a -> a) x\n(*@ ensures result = x *)") == []
