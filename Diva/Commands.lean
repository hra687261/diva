import Diva.Parser
import Diva.Interp
import Diva.AbsInt.ItvDomain
import Diva.Report
import Diva.Opt

/-!
# Command-line commands (untrusted)

Each command takes the source of a program and gives what `diva` prints. They are
pure functions, so that tests can check them. `Main` parses the arguments, reads
the file and prints.

- `run`: evaluate the program and print its value.
- `check`: say where the program may fail, or that it can't fail.
- `opt`: print the optimised program.
- `hints`: print the hints inferred for the program, one per line.
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

/-- `diva run`: the value of the program. A runtime error exits with code 1. -/
def run (src : String) : Result :=
  withParse src fun e =>
    match eval fuel [] [] e with
    | .ok v _ => { out := [Report.clean (toString v)] }
    | .err k _ => { err := [s!"runtime error: {ppErr k}"], code := 1 }
    | .outOfFuel => { err := ["out of fuel"], code := 1 }

/-- `diva check`: where the program may fail. If it may fail, exits with code 1. -/
def check (src : String) : Result :=
  withParse src fun e =>
    let H := inferHints ([] : AEnv Itv) e
    let msgs := Report.report ([] : AEnv Itv) e
    { out := msgs, code := if mayFail H [] e then 1 else 0 }

/-- `diva opt`: the optimised program. -/
def opt (src : String) : Result :=
  withParse src fun e => { out := [Report.clean (toString (Opt.optimize ([] : AEnv Itv) e))] }

/-- `diva hints`: the inferred hints, as `name : values`. `$f` is the result of the
    function `f`. Names keep their `#n` suffix: it makes them unique, and hints are
    keyed by name. -/
def hints (src : String) : Result :=
  withParse src fun e =>
    { out := (inferHints ([] : AEnv Itv) e).map fun (x, a) => s!"{x} : {a}" }

end Diva.Commands
