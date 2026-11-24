import Diva.Commands

open Diva SynthOracle

/-- The items of `src`. -/
def items (src : String) : List Item := (parseItems src).toOption.getD []

/-- `abs` is a stub, with a contract. -/
def src := "let abs x = assert false\n(*@ ensures result >= 0 *)\n;; abs 3"

#guard (stubs (items src)).map (·.1) == ["abs"]

-- the code of the stub, and a new function before it: accepted before Lean
#guard changes (items src)
  (items "let neg x = 0 - x\nlet abs x = if x < 0 then neg x else x\n(*@ ensures result >= 0 *)\n;; abs 3") ==
  none

-- a changed contract, a stub left, a changed expression, or a name defined twice: rejected
#guard (changes (items src) (items "let abs x = x\n(*@ ensures result >= x *)\n;; abs 3")).isSome
#guard (changes (items src) (items src)).isSome
#guard (changes (items src) (items "let abs x = x\n(*@ ensures result >= 0 *)\n;; abs 4")).isSome
#guard changes (items src)
  (items "let abs x = x * x\n(*@ ensures result >= 0 *)\nlet abs x = 0 - 1\n;; abs 3") ==
  some "it defines a name twice"

/-- A mock Lean, without IO: it accepts every file. -/
def lean (_ : String) : Id (Option String) := none

-- a program without a stub, or a stub without a contract
#guard (Commands.synthOracle (fun _ => ("" : Id String)) lean 1 "let f x = x").code == 1
#guard (Commands.synthOracle (fun _ => ("" : Id String)) lean 1 "let f x = assert false").err ==
  ["the stub `f` has no contract"]

-- an answer that isn't only JSON is rejected, and the oracle is asked again
#guard (Commands.synthOracle (fun _ => (src : Id String)) lean 1 src).out ==
  ["round 1: the answer of the oracle isn't in the format: the answer is not only JSON"]
