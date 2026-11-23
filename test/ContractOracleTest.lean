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
#guard needed (items src) == ["b", "a"]

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
-- no contract: write the main one first
#guard (Commands.specOracle (fun _ => ("" : Id String)) lean 1 "let f x = x").code == 1
-- an answer that isn't only JSON is rejected, and the oracle is asked again
#guard (Commands.specOracle (fun _ => (src : Id String)) lean 1 src).out ==
  ["round 1: the answer of the oracle isn't in the format: the answer is not only JSON"]
