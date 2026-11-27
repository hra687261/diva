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
- `opt`: print the optimised program. With `--cert` (`optCert`), print a Lean file
  stating that the optimised program is equivalent to the program.
- `hints`: print the hints inferred for the program, one per line.
- `cert`: print a certificate, a Lean file stating that the program can't fail.
- `prove`: print a Lean file stating that the functions meet their contracts. With an
  oracle (`proveOracle`), an LLM completes the proofs that Lean doesn't accept.
- `spec`: an LLM writes the contracts of the functions called by the functions with a
  contract (or of all the functions, if none has one), and Lean checks the file of `prove` (`specOracle`).
- `synth`: an LLM writes the code of the functions whose body is `assert false`, and
  Lean proves that it meets their contracts (`synthOracle`).

The commands that infer hints take `depth`: how deep the hints describe the parts of
lists and other ADT values (see `inferHints`).
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

/-- A parse error of the program in `file` (`msg` gives the line and the column). -/
def parseError (file : Option String) (msg : String) : Result :=
  { err := [match file with | some f => s!"{f}:{msg}" | none => msg], code := 1 }

/-- The result of `cmd` on the program `src` parses to, or a parse error. -/
def withParse (file : Option String) (src : String) (cmd : Expr → Result)
    (read : Reader := parseItemsLoc) : Result :=
  match read.expr src with
  | .ok e => cmd e
  | .error msg => parseError file msg

/-- `diva run`: parse the program `src`, run it, and print the value it returns. If
    the run fails, or takes more than `fuel` steps, print why and exit with code 1. -/
def run (src : String) (file : Option String := none)
    (read : Reader := parseItemsLoc) : Result :=
  withParse file src (read := read) fun e =>
    match eval fuel [] [] e with
    | .ok v _ => { out := [Report.clean (toString v)] }
    | .err k _ => { err := [s!"runtime error: {ppErr k}"], code := 1 }
    | .outOfFuel => { err := ["out of fuel"], code := 1 }

/-- How the reports print a span of `src`: `file:line:col-col`, or nothing without
    `file`. -/
def place (src : String) : Option String → Span → String
  | some file, sp => sp.format src file
  | none, _ => ""

/-- `diva print`: parse the program `src`, and print it as DIVA reads it: one expression,
    where the `requires` of the contracts are `assert`s. -/
def print (src : String) (file : Option String := none)
    (read : Reader := parseItemsLoc) : Result :=
  withParse file src (read := read) fun e => { out := [Report.clean (toString e)] }

/-- `diva check`: parse the program `src`, and print the places where the analysis
    says it may fail, with their positions in `file` (see `Report.report`). Exit with
    code 0 if the program can't fail, and 1 if it may. Code 0 may come from the analysis
    of arrays, refs, exceptions and the elements of lists (`mayFailExt`), which isn't
    proved yet. The message then says so. -/
def check (src : String) (file : Option String := none)
    (read : Reader := parseItemsLoc) (depth : Nat := 5) : Result :=
  match read.lexpr src with
  | .error msg => parseError file msg
  | .ok ⟨e, l⟩ =>
    let H := inferHints ([] : AEnv Itv) e (depth := depth)
    let msgs := Report.report ([] : AEnv Itv) e (l := l) (place := place src file)
      (code := Span.text src) (depth := depth)
    let fails := Report.mayFailUnproved ([] : AEnv Itv) e [] depth
    { out := msgs, code := if mayFail H [] e && fails then 1 else 0 }

/-- `diva check --oracle`: parse the program `src`, and ask `oracle` for hints, at most
    `rounds` times, until the program is safe with them (`Oracle.consult`). Print each
    round, then what `check` prints with the last hints, with the positions in `file`. -/
def checkOracle [Monad m] (oracle : String → m String) (rounds : Nat) (src : String)
    (file : Option String := none) (read : Reader := parseItemsLoc) (depth : Nat := 5) :
    m Result :=
  match read.lexpr src with
  | .error msg => return parseError file msg
  | .ok ⟨e, l⟩ => do
    let rs ← Oracle.consult oracle ([] : AEnv Itv) e rounds (file.map fun f => ⟨f, src, l⟩) depth
    let shown := rs.zipIdx.flatMap fun (r, i) =>
      [s!"round {i + 1}: the oracle proposes"] ++
        (match r.error with
         | some msg => [s!"  an answer that isn't in the format: {msg}"]
         | none =>
           if r.hints.isEmpty then ["  nothing"] else r.hints.map fun (x, a) => s!"  {x} : {a}") ++
        [if r.accepted then "accepted" else "rejected"]
    let fixed := (rs.getLast?.map (·.hints)).getD []
    let H := inferHints ([] : AEnv Itv) e fixed (depth := depth)
    let msgs := Report.report ([] : AEnv Itv) e fixed l (place src file) (Span.text src) depth
    let fails := Report.mayFailUnproved ([] : AEnv Itv) e fixed depth
    return { out := shown ++ msgs, code := if mayFail H [] e && fails then 1 else 0 }

/-- `diva opt`: parse the program `src`, optimise it using what the analysis knows
    about its values, and print the optimised program. With `infer`, each function
    without a contract first gets the contract that the analysis infers
    (`SpecOfHints.inferContracts`). Its `requires` is then checked at the start of the
    function, as for the contracts in the source. In the body, after that check, the
    optimiser knows the precondition. If the analysis proves that the program never
    fails, the checks (`assert`) are erased: they always hold. -/
def opt (src : String) (infer : Bool := false) (file : Option String := none)
    (read : Reader := parseItemsLoc) (depth : Nat := 5) : Result :=
  match read.items src with
  | .error msg => parseError file msg
  | .ok items =>
    let items := if infer then (SpecOfHints.inferContracts items depth).1 else items
    let e := (resolve [] (Item.toExpr items)).run' {}
    let H := inferHints ([] : AEnv Itv) e (depth := depth)
    { out := [Report.clean (toString (Opt.opt H (!mayFail H [] e) [] e))] }

/-- `diva opt --cert`: like `opt`, but print the certificate of the optimisation
    (`Cert.optCertificate`): a Lean file stating that the program and its optimised
    version are equivalent. -/
def optCert (src : String) (infer : Bool := false) (file : Option String := none)
    (read : Reader := parseItemsLoc) (depth : Nat := 5) : Result :=
  match read.items src with
  | .error msg => parseError file msg
  | .ok items =>
    let items := if infer then (SpecOfHints.inferContracts items depth).1 else items
    let e := (resolve [] (Item.toExpr items)).run' {}
    { out := [Cert.optCertificate (inferHints ([] : AEnv Itv) e (depth := depth)) e] }

/-- `diva hints`: parse the program `src`, infer its hints, and print them, one per
    line, as `name : values`. A hint gives the values that a function parameter can
    take, or that a function can return: `$f` is the result of the function `f`.
    Names keep their `#n` suffix: it makes them unique, and hints are keyed by name. -/
def hints (src : String) (file : Option String := none)
    (read : Reader := parseItemsLoc) (depth : Nat := 5) : Result :=
  withParse file src (read := read) fun e =>
    let H := inferHints ([] : AEnv Itv) e (ext := true) (depth := depth)
    { out := H.map fun (x, a) => s!"{x} : {a}" }

/-- `diva cert`: parse the program `src`, and print its certificate
    (`Cert.certificate`): a Lean file stating that the program never fails, with the
    hints inferred for it. If the analysis says that the program may fail, there is
    no certificate: print why and exit with code 1. -/
def cert (src : String) (file : Option String := none)
    (read : Reader := parseItemsLoc) (depth : Nat := 5) : Result :=
  withParse file src (read := read) fun e =>
    let H := inferHints ([] : AEnv Itv) e (depth := depth)
    match Cert.certificate H e with
    | some c => { out := [c] }
    | none =>
      let why := if Report.mayFailUnproved ([] : AEnv Itv) e [] depth then "the program may fail"
        else "the analysis of arrays, refs, exceptions and the elements of lists isn't proved yet"
      { err := [s!"{why}, so there is no certificate (see `diva check`)"], code := 1 }

/-- `diva prove`: parse the program `src`, and print the Lean file (`Prove.file`) that
    states and proves that its functions meet their contracts. If the program doesn't
    parse, has no contract, or has a contract that isn't supported, print why and exit
    with code 1. With `infer`, each function without a contract gets the contract that
    the analysis infers (`SpecOfHints.inferContracts`). -/
def prove (src : String) (infer : Bool := false) (file : Option String := none)
    (read : Reader := parseItemsLoc) (depth : Nat := 5) : Result :=
  match read.items src with
  | .error msg => parseError file msg
  | .ok items =>
    let (items, inferred) := if infer then SpecOfHints.inferContracts items depth else (items, [])
    match Prove.file items (inferred := inferred) with
    | .ok f => { out := [f] }
    | .error msg => { err := [msg], code := 1 }

/-- `diva prove --oracle`: build the Lean file of `src` (`Prove.file`) and check it with
    `lean`. Each proof that Lean doesn't accept is replaced by one from `oracle`, with
    at most `rounds` questions in all (`ProveOracle.consult`). `check` says why a proof
    from `oracle` can't be used (see `ParseProof.check`).
    Exit with code 1 if Lean doesn't accept the last file. -/
def proveOracle [Monad m] (oracle : String → m String) (lean : String → m (Option String))
    (check : String → Option String) (rounds : Nat) (src : String)
    (file : Option String := none) (read : Reader := parseItemsLoc) : m Result := do
  match read.items src with
  | .error msg => return parseError file msg
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
    (rounds : Nat) (src : String)
    (file : Option String := none) (read : Reader := parseItemsLoc) : m Result := do
  match read.items src with
  | .error msg => return parseError file msg
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
    (rounds : Nat) (src : String)
    (file : Option String := none) (read : Reader := parseItemsLoc) : m Result := do
  match read.items src with
  | .error msg => return parseError file msg
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
