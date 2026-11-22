import Diva.Commands
import Diva.CheckFile

open Diva ProveOracle Lean

/-- An answer with the proof `lines`, one tactic per line. -/
def proof (lines : List String) : String :=
  (json% {"proof": $(lines.toArray)}).compress

/-- The proof in `answer`, or the line `error: ...` that says why `answer` is rejected. -/
def proofIn (answer : String) : String :=
  match parseProof answer with
  | .ok p => p
  | .error msg => s!"error: {msg}"

-- the proof in an answer `{"proof": [...]}`, one tactic per line
#guard proofIn (proof ["simp", "· omega", "  rfl"]) == "simp\n· omega\n  rfl"

-- any other answer is rejected
#guard proofIn "```lean\nomega\n```" == "error: the answer is not only JSON"
#guard proofIn (json% {"tactics": ["omega"]}).compress ==
  "error: the answer has no list of lines `proof`"
#guard proofIn (proof []) == "error: the proof is empty"

open Elab Command in
/-- Print why `ParseProof.check` rejects `proof`, or `ok`. The tactics are those of
    this file. -/
def showCheck (proof : String) : CommandElabM Unit := do
  logInfo ((ParseProof.check (← getEnv) proof).getD "ok")

-- the proof is parsed with Lean's parser: it must be tactics only
/-- info: ok -/
#guard_msgs in #eval showCheck "intro x\n· simp\n  omega"
/-- info: it isn't only tactics: <proof>:3:2: expected end of input -/
#guard_msgs in #eval showCheck "omega\ndef bad := 1"

-- proofs that could make Lean accept a false theorem are rejected
/-- info: it uses `sorry` -/
#guard_msgs in #eval showCheck "exact (by sorry)"
/-- info: it uses `native_decide` -/
#guard_msgs in #eval showCheck "native_decide"
/-- info: it uses `set_option` -/
#guard_msgs in #eval showCheck "set_option debug.skipKernelTC true in omega"
/-- info: it uses `stop` -/
#guard_msgs in #eval showCheck "stop\nrfl"

-- comments and strings are not checked
/-- info: ok -/
#guard_msgs in #eval showCheck "omega -- not sorry"

-- the obligation of an error: the last `theorem` before the error's line
#guard failing "def a := 1\ntheorem f_body : X := by\n  omega\ntheorem f_correct : Y := Z"
  "p.lean:3:2: error: omega could not prove the goal" == ["f_body"]
#guard failing "theorem f_correct : Y := Z" "p.lean:1:0: error: bad" == []

/-- `square` returns `x * x`: `omega` can't prove its contract. -/
def src := "let square x = x * x\n(*@ ensures result >= 0 *)"

/-- A mock Lean, without IO: it accepts a file if it contains `good`. -/
def lean (file : String) : Id (Option String) :=
  if (file.splitOn "good").length ≥ 2 then none
  else
    let n := ((file.splitOn "\n").zipIdx.find? (·.1.startsWith "theorem square_body")).map (·.2 + 2)
    some s!"prove.lean:{n.getD 0}:2: error: omega could not prove the goal"

/-- A stand-in for `ParseProof.check`: it rejects the proof `sorry`. -/
def check (proof : String) : Option String :=
  if proof == "sorry" then some "it uses `sorry`" else none

-- the oracle's proof is accepted
#guard (Commands.proveOracle (fun _ => (proof ["exact good"] : Id String)) lean check 3 src).code == 0
-- a forbidden proof is rejected, and the oracle is asked again
#guard (Commands.proveOracle (fun _ => (proof ["sorry"] : Id String)) lean check 2 src).out ==
  ["round 1: the oracle proposes a proof of `square_body`", "  sorry", "rejected: it uses `sorry`",
   "round 2: the oracle proposes a proof of `square_body`", "  sorry", "rejected: it uses `sorry`"]
-- an answer that isn't in the format is rejected, and the oracle is asked again
#guard (Commands.proveOracle (fun _ => ("omega" : Id String)) lean check 1 src).out ==
  ["round 1: the answer of the oracle isn't in the format: the answer is not only JSON"]

/-- The axioms that the theorem `n` uses, other than the standard ones. -/
def axiomsOf (n : Name) : Elab.Command.CommandElabM Unit := do
  IO.println (CheckFile.otherAxioms (← getEnv) n)

theorem proved : 1 + 1 = 2 := by omega

/-- info: [] -/
#guard_msgs in #eval axiomsOf `proved

-- Lean only warns about `sorry`. `CheckFile.run` makes it an error, because of `sorryAx`.
#guard_msgs (drop warning) in
theorem uses_stop : 1 = 2 := by
  stop
  rfl

/-- info: [sorryAx] -/
#guard_msgs in #eval axiomsOf `uses_stop

-- `decide +native` has no word of `ParseProof.forbidden`, but its axiom is found
theorem native : 2 + 2 = 4 := by decide +native

/-- info: [native._native.decide.ax_1_1] -/
#guard_msgs in #eval axiomsOf `native
