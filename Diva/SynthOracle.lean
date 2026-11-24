import Diva.ContractOracle

/-!
# LLM code from contracts for `diva synth` (untrusted)

The user writes a function without its code, a stub: `let f x = assert false`,
followed by its contract. An oracle (an LLM) writes the code, and Lean proves that
it meets the contract.

- `stubs` lists the stubs of a program. Each must have a contract.
- `changes` rejects an answer that changes the rest of the program or a contract of
  the user, that leaves a stub, or that defines a name twice.
- `consult` asks the oracle for the whole program, at most `rounds` times, until Lean
  accepts the file of `diva prove` for it (`ContractOracle.consultWith`).

Here the contracts come from the user. So the proof says that the code does what the
user asked for.
-/

namespace Diva.SynthOracle

open ContractOracle

/-- `b` is a stub: `let f x = assert false` or `let rec f x = assert false`. -/
def isStub : Binding → Bool
  | .val _ (.lam _ (.assert (.bool false))) | .recFn _ _ (.assert (.bool false)) => true
  | _ => false

/-- The stubs of `items`, with their contracts (`none` if a stub has none). -/
def stubs (items : List Item) : List (String × Option Spec) :=
  items.filterMap fun
    | .decl b sp => if isStub b then some (b.name, sp) else none
    | .expr _ => none

/-- The answer `l` is right for the item `u` of the user: `l` is `u`, or, if `u` is a
    stub, `l` is a function of the same name and contract that isn't a stub. -/
def fits (u l : Item) : Bool :=
  match u, l with
  | .decl b sp, .decl b' sp' =>
    if isStub b then b'.name == b.name && sp' == sp && !isStub b' else u == l
  | _, _ => u == l

/-- The items `us` of the user appear in `ls`, in the same order (`fits`). `ls` may
    have more items: the functions that the oracle adds. -/
def keeps : List Item → List Item → Bool
  | [], _ => true
  | _ :: _, [] => false
  | u :: us, l :: ls => if fits u l then keeps us ls else keeps (u :: us) ls

/-- Why the program `ls` of the oracle is rejected without running Lean, if it is. -/
def changes (us ls : List Item) : Option String :=
  let names := ls.filterMap fun | .decl b _ => some b.name | .expr _ => none
  if !keeps us ls then
    some "it changes the program outside the stubs, or a contract, or it leaves a stub"
  else if names.eraseDups.length != names.length then some "it defines a name twice"
  else none

/-- The question to the oracle about the program `src`, whose stubs are `fs`.
    `previous` is the previous answer, and why it was rejected. -/
def prompt (src : String) (fs : List String) (previous : Option (String × String)) :
    String :=
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
A contract is written after each function: `(*@ r = f x requires ... ensures ... *)`.

In this program, these functions have no code yet: their body is `assert false`.
{", ".intercalate (fs.map (s!"`{·}`"))}. Write their code, so that each one meets its contract.

```
{src}
```
{rejected}
The code can use integers, `let`, `if`, `+`, `-`, `*`, comparisons and `&&`, and
calls. A function has one integer parameter. A recursive function is `let rec f x =
...`. You can add functions before the stubs. A function called by a function with
a contract needs a contract too. Don't change the contracts or the rest of the
program.

Answer with JSON only, in this format, with the whole program, one line of the program
per string:

  \{\"program\": [\"let f x = x + 1\", \"(*@ r = f x ensures r > x *)\", ...]}"

/-- Ask `oracle` for the code of the stubs of the program `src` (its items are `items`),
    at most `rounds` times, until Lean accepts the file of `diva prove` for the
    program. `lean` checks a file: `none` if Lean accepts it, or Lean's errors. -/
def consult [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (src : String) (items : List Item) (rounds : Nat) : m ContractOracle.Outcome :=
  consultWith oracle lean (prompt src ((stubs items).map (·.1))) (changes items) (fun _ => [])
    rounds

end Diva.SynthOracle
