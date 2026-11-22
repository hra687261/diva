import Diva.Prove
import Diva.Answer
import Diva.ParseProof

/-!
# LLM proofs for `diva prove` (untrusted)

When Lean rejects the proof of an obligation `f_body` in the file of `diva prove`,
an oracle (an LLM) writes another proof. Lean checks it.

- `failing` finds the obligations whose proof Lean rejects, from Lean's errors.
- `prompt` is the question: the file, the obligation, and Lean's errors.
- `parseProof` reads the answer, which must be JSON only: `{"proof": ["simp", "omega"]}`,
  one tactic per line.
- `check` (given by `diva`, see `ParseProof.check`) parses the proof with Lean's
  parser. It rejects a proof that isn't only tactics, or that uses a keyword that
  could make Lean accept a false theorem, or run code: `sorry`, `native_decide`,
  `set_option`, `run_tac`, ...
- `lean` (given by `diva`, see `CheckFile.run`) checks the file, and then the axioms
  of its theorems. A proof that uses `sorry` or another axiom is an error. This catches
  what `check` misses, such as `exact sorryAx _ false`.
- `consult` asks the oracle, at most `rounds` times, until Lean accepts the file.

Only the proofs come from the oracle. The statements (`f_fn`, `f_body`,
`f_correct`) are written by `diva prove`, so a proof from the oracle can't change
what is proved.
-/

namespace Diva.ProveOracle

/-- The line numbers of Lean's errors: the lines `file:line:col: error...`. -/
def errorLines (errors : String) : List Nat :=
  (errors.splitOn "\n").filterMap fun l =>
    if (l.splitOn ": error").length < 2 then none
    else match l.splitOn ":" with
      | _ :: n :: _ => n.toNat?
      | _ => none

/-- The obligations (`f_body`) of `file` that contain an error of `errors`. An error
    belongs to the last line `theorem ...` before it. -/
def failing (file errors : String) : List String :=
  let lines := (file.splitOn "\n").zipIdx
  let names := (errorLines errors).filterMap fun n =>
    let before := lines.filter fun (l, i) => i + 1 ≤ n && l.startsWith "theorem "
    before.getLast?.bind fun (l, _) =>
      let name := ((l.drop 8).toString.splitOn " ").headD ""
      if name.endsWith "_body" then some name else none
  names.eraseDups

/-- The proof in an answer `{"proof": [line, ...]}`: the lines, one tactic per line.
    Any other answer is an error. -/
def parseProof (answer : String) : Except String String := do
  let j ← Answer.json answer
  let lines ← (j.getObjValAs? (Array String) "proof").mapError fun _ =>
    "the answer has no list of lines `proof`"
  if lines.all (·.trimAscii.isEmpty) then throw "the proof is empty"
  return "\n".intercalate lines.toList

/-- The question to the oracle: write a proof of the obligation `name` of `file`, which
    Lean rejects with `errors`. `rejected` says why the previous answer was rejected,
    if it was rejected before Lean checked it. -/
def prompt (file name errors : String) (rejected : Option String) : String :=
  let rejected := match rejected with
    | none => ""
    | some why => s!"\nYour previous answer was rejected: {why}\n"
  s!"DIVA wrote this Lean 4 file to prove that OCaml functions meet their contracts.
Lean rejects the proof of `{name}`.

The file:

```lean
{file}
```

Lean's errors:

{errors}
{rejected}
Write a new proof of `{name}`: the tactics after `:= by`. Only Lean's core library
is available (no Mathlib). The proof can't use `sorry`, `stop`, `native_decide`,
`set_option`, `run_tac`, `by_elab` or `unsafe`. It must be tactics only.

Answer with JSON only, in this format, with one tactic per line:

  \{\"proof\": [\"intro x hx\", \"simp [f_fn]\", \"omega\"]}

Keep the indentation of nested tactics in the lines, such as `  omega` after `·`."

/-- What `consult` gives: the rounds, one line each, and Lean's errors on the last file,
    or `none` if Lean accepts it. -/
structure Outcome where
  log : List String
  errors : Option String

/-- Write the file of `diva prove` for the program `items`, and check it with `lean`
    (`none`: accepted, or Lean's errors). If Lean rejects the proof of an obligation,
    ask `oracle` for another one, at most `rounds` times. `check` says why a proof from
    `oracle` can't be used, or gives `none` if it can. -/
def consult [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (check : String → Option String) (items : List Item) (rounds : Nat) :
    ExceptT String m Outcome :=
  go rounds 1 [] [] none
where
  go : Nat → Nat → List (String × String) → List String → Option String →
      ExceptT String m Outcome
    | k, i, proofs, log, rejected => do
      let file ← liftExcept (Prove.file items proofs)
      let some errors ← (lean file : m _) | return ⟨log, none⟩
      match failing file errors, k with
      | name :: _, k + 1 => do
        let answer ← (oracle (prompt file name errors rejected) : m _)
        match parseProof answer with
        | .error msg =>
          let log := log ++ [s!"round {i}: the answer of the oracle isn't in the format: {msg}"]
          go k (i + 1) proofs log (some s!"it isn't in the format: {msg}")
        | .ok proof =>
          let log := log ++ [s!"round {i}: the oracle proposes a proof of `{name}`"] ++
            (proof.splitOn "\n").map ("  " ++ ·)
          match check proof with
          | none =>
            let proof := "\n".intercalate ((proof.splitOn "\n").map ("  " ++ ·))
            go k (i + 1) ((name, proof) :: proofs) log none
          | some why => go k (i + 1) proofs (log ++ [s!"rejected: {why}"]) (some why)
      | _, _ => return ⟨log, some errors⟩
  liftExcept {α} : Except String α → ExceptT String m α
    | .ok a => pure a
    | .error e => throw e

end Diva.ProveOracle
