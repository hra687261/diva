import Diva.Parser
import Diva.Interp
import Diva.AbsInt.ItvDomain
import Diva.Report
import Diva.Opt
import Diva.Cert
import Diva.Prove
import Diva.SpecOfHints
import Diva.Oracle
import Diva.ProveOracle
import Diva.ContractOracle
import Diva.SynthOracle

/-!
# Command-line commands (untrusted)

Each command takes the source of a program and gives what `diva` prints. They are
pure functions, so that tests can check them. `Main` parses the arguments, reads
the file and prints.

- `run`: evaluate the program and print its value.
- `check`: say where the program may fail, or that it can't fail. With an oracle
  (`checkOracle`), if the check fails, an LLM is told where, and proposes hints.
- `opt`: print the optimised program.
- `hints`: print the hints inferred for the program, one per line.
- `cert`: print a certificate, a Lean file stating that the program can't fail.
- `prove`: print a Lean file stating that the functions meet their contracts. With an
  oracle (`proveOracle`), an LLM completes the proofs that Lean doesn't accept.
- `spec`: an LLM writes the contracts of the functions called by the functions with a
  contract (or of all the functions, if none has one), and Lean checks the file of `prove` (`specOracle`).
- `synth`: an LLM writes the code of the functions whose body is `assert false`, and
  Lean proves that it meets their contracts (`synthOracle`).
-/

namespace Diva.Commands

open AbsInt

/-- What a command prints: lines on the standard output, lines on the standard
    error, and the exit code. -/
structure Result where
  out : List String := []
  err : List String := []
  code : UInt32 := 0
  deriving Inhabited, BEq, Repr

/-- Evaluation fuel bound. -/
def fuel : Nat := 100000
-- TODO: should be determined through the cli, and the default value should be
-- set there

/-- The result of `cmd` on the program `src` parses to, or a parse error. -/
def withParse (src : String) (cmd : Expr → Result) : Result :=
  match parse src with
  | .ok e => cmd e
  | .error msg => { err := [s!"parse error: {msg}"], code := 1 }

/-- `diva run`: parse the program `src`, run it, and print the value it returns. If
    the run fails, or takes more than `fuel` steps, print why and exit with code 1. -/
def run (src : String) : Result :=
  withParse src fun e =>
    match eval fuel [] [] e with
    | .ok v _ => { out := [Report.clean (toString v)] }
    | .err k _ => { err := [s!"runtime error: {ppErr k}"], code := 1 }
    | .outOfFuel => { err := ["out of fuel"], code := 1 }

/-- `diva check`: parse the program `src`, and print the places where the analysis
    says it may fail. Exit with code 1 if it may fail, and 0 if it can't. -/
def check (src : String) : Result :=
  withParse src fun e =>
    let H := inferHints ([] : AEnv Itv) e
    let msgs := Report.report ([] : AEnv Itv) e
    { out := msgs, code := if mayFail H [] e then 1 else 0 }

/-- `diva check --oracle`: parse the program `src`, and ask `oracle` for hints, at most
    `rounds` times, until the program is safe with them (`Oracle.consult`). Print each
    round, then what `check` prints with the last hints. -/
def checkOracle [Monad m] (oracle : String → m String) (rounds : Nat) (src : String) :
    m Result :=
  match parse src with
  | .error msg => return { err := [s!"parse error: {msg}"], code := 1 }
  | .ok e => do
    let rs ← Oracle.consult oracle ([] : AEnv Itv) e rounds
    let shown := rs.zipIdx.flatMap fun (r, i) =>
      [s!"round {i + 1}: the oracle proposes"] ++
        (match r.error with
         | some msg => [s!"  an answer that isn't in the format: {msg}"]
         | none =>
           if r.hints.isEmpty then ["  nothing"] else r.hints.map fun (x, a) => s!"  {x} : {a}") ++
        [if r.accepted then "accepted" else "rejected"]
    let fixed := (rs.getLast?.map (·.hints)).getD []
    let H := inferHints ([] : AEnv Itv) e fixed
    return { out := shown ++ Report.report ([] : AEnv Itv) e fixed,
             code := if mayFail H [] e then 1 else 0 }

/-- `diva opt`: parse the program `src`, optimise it using what the analysis knows
    about its values, and print the optimised program. With `infer`, each function
    without a contract first gets the contract that the analysis infers
    (`SpecOfHints.inferContracts`). Its `requires` is then checked at the start of the
    function, as for the contracts in the source. In the body, after that check, the
    optimiser knows the precondition. -/
def opt (src : String) (infer : Bool := false) : Result :=
  match parseItems src with
  | .error msg => { err := [s!"parse error: {msg}"], code := 1 }
  | .ok items =>
    let items := if infer then (SpecOfHints.inferContracts items).1 else items
    let e := (resolve [] (Item.toExpr items)).run' {}
    { out := [Report.clean (toString (Opt.optimize ([] : AEnv Itv) e))] }

/-- `diva hints`: parse the program `src`, infer its hints, and print them, one per
    line, as `name : values`. A hint gives the values that a function parameter can
    take, or that a function can return: `$f` is the result of the function `f`.
    Names keep their `#n` suffix: it makes them unique, and hints are keyed by name. -/
def hints (src : String) : Result :=
  withParse src fun e =>
    { out := (inferHints ([] : AEnv Itv) e).map fun (x, a) => s!"{x} : {a}" }

/-- `diva cert`: parse the program `src`, and print its certificate
    (`Cert.certificate`): a Lean file stating that the program never fails, with the
    hints inferred for it. If the analysis says that the program may fail, there is
    no certificate: print why and exit with code 1. -/
def cert (src : String) : Result :=
  withParse src fun e =>
    match Cert.certificate (inferHints ([] : AEnv Itv) e) e with
    | some c => { out := [c] }
    | none => { err := ["the program may fail, so there is no certificate (see `diva check`)"],
                code := 1 }

/-- `diva prove`: parse the program `src`, and print the Lean file (`Prove.file`) that
    states and proves that its functions meet their contracts. If the program doesn't
    parse, has no contract, or has a contract that isn't supported, print why and exit
    with code 1. With `infer`, each function without a contract gets the contract that
    the analysis infers (`SpecOfHints.inferContracts`). -/
def prove (src : String) (infer : Bool := false) : Result :=
  match parseItems src with
  | .error msg => { err := [s!"parse error: {msg}"], code := 1 }
  | .ok items =>
    let (items, inferred) := if infer then SpecOfHints.inferContracts items else (items, [])
    match Prove.file items (inferred := inferred) with
    | .ok f => { out := [f] }
    | .error msg => { err := [msg], code := 1 }

/-- `diva prove --oracle`: build the Lean file of `src` (`Prove.file`) and check it with
    `lean`. Each proof that Lean doesn't accept is replaced by one from `oracle`, with
    at most `rounds` questions in all (`ProveOracle.consult`). `check` says why a proof
    from `oracle` can't be used (see `ParseProof.check`).
    Exit with code 1 if Lean doesn't accept the last file. -/
def proveOracle [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (check : String → Option String) (rounds : Nat) (src : String) : m Result := do
  match parseItems src with
  | .error msg => return { err := [s!"parse error: {msg}"], code := 1 }
  | .ok items =>
    match ← (ProveOracle.consult oracle lean check items rounds).run with
    | .error msg => return { err := [msg], code := 1 }
    | .ok ⟨log, none⟩ => return { out := log ++ ["checked by Lean: the functions meet their contracts, and the top-level expressions don't fail"] }
    | .ok ⟨log, some errors⟩ => return { out := log, err := [errors], code := 1 }

/-- `diva spec --oracle`: parse the program `src`, and ask `oracle` for the contracts of
    the functions that the functions with a contract call (`ContractOracle.consult`),
    at most `rounds` times. If no function has a contract, ask for the contracts of all
    the functions. `lean` checks the file of `prove` for the program with these
    contracts (`none`: accepted, or Lean's errors). Print each round, then the program
    with the new contracts. Exit with code 1 if no answer is accepted. -/
def specOracle [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (rounds : Nat) (src : String) : m Result := do
  match parseItems src with
  | .error msg => return { err := [s!"parse error: {msg}"], code := 1 }
  | .ok items =>
    if ContractOracle.toSpecify items |>.isEmpty then
      let msg := if ContractOracle.noContract items then "the program has no function"
        else "the functions called by the functions with a contract have one: use `diva prove`"
      return { err := [msg], code := 1 }
    let r ← ContractOracle.consult oracle lean src items rounds
    match r.program with
    | some prog =>
      let warning := if ContractOracle.noContract items then
          ["", "warning: the oracle wrote all the contracts. Read them to know what is proved."]
        else []
      return { out := r.log ++ warning ++ ["", prog] }
    | none => return { out := r.log, err := [r.errors], code := 1 }

/-- `diva synth --oracle`: parse the program `src`, and ask `oracle` for the code of its
    stubs, the functions `let f x = assert false` (`SynthOracle.consult`), at most
    `rounds` times. `lean` checks the file of `prove` for the program with this code
    (`none`: accepted, or Lean's errors). Print each round, then the program. Exit with
    code 1 if no answer is accepted. -/
def synthOracle [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (rounds : Nat) (src : String) : m Result := do
  match parseItems src with
  | .error msg => return { err := [s!"parse error: {msg}"], code := 1 }
  | .ok items =>
    let fs := SynthOracle.stubs items
    if fs.isEmpty then
      return { err := ["no function to write: write `let f x = assert false`, then its contract"],
               code := 1 }
    if let some (f, _) := fs.find? (·.2.isNone) then
      return { err := [s!"the stub `{f}` has no contract"], code := 1 }
    let r ← SynthOracle.consult oracle lean src items rounds
    match r.program with
    | some prog => return { out := r.log ++ ["", prog] }
    | none => return { out := r.log, err := [r.errors], code := 1 }

end Diva.Commands
