import Diva.Prove
import Diva.Answer

/-!
# LLM contracts for `diva spec` (untrusted)

The user writes the contract of a function `f`. To prove it, `diva prove` needs the
contracts of the functions that `f` calls. Here an oracle (an LLM) writes them.

- `needed` lists the functions without a contract that need one: those called by a
  function with a contract, or by a function in that list.
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

/-- The names used in `e`. It may also give names defined in `e`. -/
def names : Expr → List String
  | .int _ | .bool _ | .unit | .nil => []
  | .var x => [x]
  | .lam _ b | .assert b | .len b | .ref _ b | .deref b | .exn _ b | .raise b => names b
  | .app a b | .binop _ a b | .cons a b | .get a b | .assign a b | .letin _ a b
  | .alloc _ a b | .letrec _ _ a b | .tryw a _ b => names a ++ names b
  | .ite a b c | .set a b c | .matchList a b _ _ c | .exnCase a _ _ b c =>
    names a ++ names b ++ names c

/-- The item `i` without its contract. -/
def code : Item → Item
  | .decl b _ => .decl b none
  | i => i

/-- The body of a declaration. -/
def body : Binding → Expr
  | .val _ e | .recFn _ _ e => e

/-- The functions of `items` without a contract that need one: those called by a
    function with a contract, or by a function of this list. -/
def needed (items : List Item) : List String :=
  let decls := items.filterMap fun | .decl b sp => some (b, sp.isSome) | .expr _ => none
  let step (need : List String) : List String :=
    need ++ (decls.flatMap fun (b, has) =>
      if has || need.contains b.name then
        (names (body b)).filter fun y =>
          !need.contains y && decls.any fun (c, hasC) => c.name == y && !hasC
      else []).eraseDups
  (decls.foldl (fun need _ => step need) []).eraseDups

/-- The term `t` as Gospel. -/
def termText : Term → String
  | .int n => toString n
  | .var x => x
  | .binop op a b => s!"({termText a} {ppBinOp op} {termText b})"
  | .and a b => s!"({termText a} && {termText b})"

/-- The contract `sp` of the function `f` as Gospel, on one line. -/
def specText (f : String) (sp : Spec) : String :=
  let header := s!"{sp.result} = {sp.name.getD f} {" ".intercalate sp.params}"
  let rs := sp.requires.map fun t => s!" requires {termText t}"
  let es := sp.ensures.map fun t => s!" ensures {termText t}"
  s!"(*@ {header.trimAscii}{String.join rs}{String.join es} *)"

/-- The program in an answer `{"program": [line, ...]}`: the lines, joined. Any other
    answer is an error. -/
def parseProgram (answer : String) : Except String String := do
  let j ← Answer.json answer
  let lines ← (j.getObjValAs? (Array String) "program").mapError fun _ =>
    "the answer has no list of lines `program`"
  return "\n".intercalate lines.toList

/-- The question to the oracle about the program `src`. `need` are the functions that
    need a contract. `previous` is the previous answer, and why it was rejected. -/
def prompt (src : String) (need : List String) (previous : Option (String × String)) :
    String :=
  let rejected := match previous with
    | none => ""
    | some (prog, why) => s!"
Your previous answer was rejected:

```
{prog}
```

Why:

{why}
"
  s!"DIVA proves that functions in a small ML-like language meet their contracts.
A contract is written after each function: `(*@ r = f x requires ... ensures ... *)`.
It can use integers, the parameter, the result, `+`, `-`, `*`, comparisons and `&&`. The
parameter and the result are integers.

To prove the contracts of this program, DIVA needs a contract for each function
that they call. These functions have none: {", ".intercalate (need.map (s!"`{·}`"))}.

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
    | (.decl _ none, .decl b (some sp)) => some s!"  {specText b.name sp}"
    | _ => none

/-- Why the program `items'` of the oracle is rejected without running Lean: it changes
    the code of `items`, or a contract of `items`. -/
def changes (items items' : List Item) : Option String :=
  if items.map code != items'.map code then some "it changes the code"
  else (items.zip items').findSome? fun
    | (.decl b (some sp), .decl _ sp') =>
      if sp' != some sp then some s!"it changes the contract of `{b.name}`" else none
    | _ => none

/-- Ask `oracle` for the contracts of the functions `needed` by the program `src`,
    at most `rounds` times, until Lean accepts the file of `diva prove` for the
    program. `lean` checks a file: `none` if Lean accepts it, or Lean's errors. -/
def consult [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (src : String) (items : List Item) (rounds : Nat) : m Outcome :=
  go rounds 1 none []
where
  go : Nat → Nat → Option (String × String) → List String → m Outcome
    | 0, _, previous, log => return ⟨log, none, (previous.map (·.2)).getD ""⟩
    | k + 1, i, previous, log => do
      let answer ← oracle (prompt src (needed items) previous)
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
          let log := log ++ newSpecs items items'
          if let some why := changes items items' then
            go k (i + 1) (some (prog, why)) (log ++ [s!"rejected: {why}"])
          else match Prove.file items' with
            | .error msg => go k (i + 1) (some (prog, msg)) (log ++ [s!"rejected: {msg}"])
            | .ok file =>
              match ← lean file with
              | none => return ⟨log ++ ["accepted"], some prog, ""⟩
              | some errors =>
                go k (i + 1) (some (prog, errors)) (log ++ ["rejected by Lean"])

end Diva.ContractOracle
