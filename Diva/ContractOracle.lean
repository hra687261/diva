import Diva.Prove
import Diva.Grammar
import Diva.Answer

/-!
# LLM contracts for `diva spec` (untrusted)

The user writes the contract of a function `f`. To prove it, `diva prove` needs the
contracts of the functions that `f` calls. Here an oracle (an LLM) writes them.

- `calledWithoutContract` lists the functions without a contract that need one: those called by a
  function with a contract, or by a function in that list. If no function has a
  contract, all the functions need one (`functions`).
- `prompt` is the question: the program, the functions that need a contract, and
  why the previous answer was rejected.
- `consult` asks the oracle, at most `rounds` times, for the whole program with the
  new contracts, until Lean accepts the file of `diva prove` for it.

The answer is rejected if it changes the code, or a contract written by the user.
So the contracts written by the user are the ones proved. The new contracts are only
the steps of the proof.

TODO: allow for hints/suggestions, when generating intermediary-function contracts
is not enough to prove the program, the llm should give the user hints on what
to do. (similar things can be applied to other interactions with llms)
-/

namespace Diva.ContractOracle

export Prove (calledWithoutContract)

/-- The item `i` without its contract. -/
def code : Item → Item
  | .decl b _ => .decl b none
  | i => i

/-- The functions of `items`: the declarations `let rec f x = ...` and `let f x = ...`. -/
def functions (items : List Item) : List String :=
  items.filterMap fun
    | .decl (.recFn f _ _) _ | .decl (.val f (.lam ..)) _ => some f
    | _ => none

/-- No item of `items` has a contract. -/
def noContract (items : List Item) : Bool :=
  items.all fun | .decl _ sp => sp.isNone | .expr _ => true

/-- The functions of `items` that need a contract: `calledWithoutContract`, or all the functions if no
    function has a contract. -/
def toSpecify (items : List Item) : List String :=
  if noContract items then functions items else calledWithoutContract items

/-- The term `t` as Gospel. -/
def termText : Term → String
  | .int n => toString n
  | .var x => x
  | .bool b => toString b
  | .binop op a b => s!"({termText a} {ppBinOp op} {termText b})"
  | .and a b => s!"({termText a} && {termText b})"
  | .or a b => s!"({termText a} || {termText b})"
  | .not a => s!"(not {termText a})"
  | .length a => s!"(length {termText a})"

/-- The contract `sp` as Gospel, on one line. -/
def specText (sp : Spec) : String :=
  let header := match sp.name with
    | some g => [" ".intercalate (sp.result :: "=" :: g :: sp.params)]
    | none => []
  let rs := sp.requires.map fun t => s!"requires {termText t}"
  let es := sp.ensures.map fun t => s!"ensures {termText t}"
  "(*@ " ++ " ".intercalate (header ++ rs ++ es) ++ " *)"

/-- The program in an answer `{"program": [line, ...]}`: the lines, joined. Any other
    answer is an error. -/
def parseProgram (answer : String) : Except String String := do
  let j ← Answer.json answer
  let lines ← (j.getObjValAs? (Array String) "program").mapError fun _ =>
    "the answer has no list of lines `program`"
  return "\n".intercalate lines.toList

/-- The question to the oracle about the program `src`. `need` are the functions that
    need a contract. `scratch` says that no function has one yet. `previous` is the
    previous answer, and why it was rejected. -/
def prompt (src : String) (need : List String) (scratch : Bool)
    (previous : Option (String × String)) : String :=
  let need := ", ".intercalate (need.map (s!"`{·}`"))
  let task := if scratch then
      s!"This program has no contract. Write a contract for each function: {need}. Each
contract says what the function computes, as precisely as you can."
    else
      s!"To prove the contracts of this program, DIVA needs a contract for each function
that they call. These functions have none: {need}."
  let rejected := match previous with
    | none => ""
    | some (prog, reason) => s!"
Your previous answer was rejected:

```
{prog}
```

Why:

{reason}
"
  s!"DIVA proves that functions in a small ML-like language meet their contracts.

{grammar}

{task}

```
{src}
```
{rejected}
Write a contract after each of these functions, so that every contract can be
proved. Don't change the code or the existing contracts.

Answer with JSON only, in this format, with the whole program, one line of the program
per string:

  \{\"program\": [\"let f x = x + 1\", \"(*@ r = f x ensures r > x *)\", ...]}"

/-- What `consult` gives: the rounds, the accepted program if there is one, and why
    the last answer was rejected otherwise. -/
structure Outcome where
  log : List String
  program : Option String
  errors : String := ""

/-- The new contracts of `items'` (they are not in `items`), one line each. -/
def newSpecs (items items' : List Item) : List String :=
  (items.zip items').filterMap fun
    | (.decl _ none, .decl b (some sp)) => some s!"  {b.name}: {specText sp}"
    | _ => none

/-- Why the program `items'` of the oracle is rejected without running Lean: it changes
    the code of `items`, or a contract of `items`. -/
def changes (items items' : List Item) : Option String :=
  if items.map code != items'.map code then some "it changes the code"
  else (items.zip items').findSome? fun
    | (.decl b (some sp), .decl _ sp') =>
      if sp' != some sp then some s!"it changes the contract of `{b.name}`" else none
    | _ => none

/-- Ask `oracle` for a program, at most `rounds` times, until Lean accepts the file of
    `diva prove` for it. `ask previous` is the question, where `previous` is the
    previous answer and why it was rejected. `changes` says why an answer is rejected
    before running Lean, if it is. `describe` gives the lines that describe an answer.
    `lean` checks a file: `none` if Lean accepts it, or Lean's errors. -/
def consultWith [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (ask : Option (String × String) → String) (changes : List Item → Option String)
    (describe : List Item → List String) (rounds : Nat) : m Outcome :=
  go rounds 1 none []
where
  go : Nat → Nat → Option (String × String) → List String → m Outcome
    | 0, _, previous, log => return ⟨log, none, (previous.map (·.2)).getD ""⟩
    | k + 1, i, previous, log => do
      let answer ← oracle (ask previous)
      match parseProgram answer with
      | .error msg =>
        let log := log ++ [s!"round {i}: the answer of the oracle isn't in the format: {msg}"]
        go k (i + 1) (some (answer, s!"it isn't in the format: {msg}")) log
      | .ok prog =>
        let log := log ++ [s!"round {i}: the oracle proposes"]
        match parseItems prog with
        | .error msg =>
          go k (i + 1) (some (prog, s!"it doesn't parse: {msg}")) (log ++ ["rejected: it doesn't parse"])
        | .ok items' =>
          let log := log ++ describe items'
          if let some why := changes items' then
            go k (i + 1) (some (prog, why)) (log ++ [s!"rejected: {why}"])
          else match Prove.file items' with
            | .error msg => go k (i + 1) (some (prog, msg)) (log ++ [s!"rejected: {msg}"])
            | .ok file =>
              match ← lean file with
              | none => return ⟨log ++ ["accepted"], some prog, ""⟩
              | some errors =>
                go k (i + 1) (some (prog, errors)) (log ++ ["rejected by Lean"])

/-- Ask `oracle` for the contracts of the functions of `toSpecify` in the program `src`
    (its items are `items`), at most `rounds` times, until Lean accepts the file of
    `diva prove` for the program. `lean` checks a file: `none` if Lean accepts it, or
    Lean's errors. -/
def consult [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (src : String) (items : List Item) (rounds : Nat) : m Outcome :=
  consultWith oracle lean (prompt src (toSpecify items) (noContract items)) (changes items)
    (newSpecs items) rounds

end Diva.ContractOracle
