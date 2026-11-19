import Diva

open Diva

/-- Evaluation fuel bound. -/
def fuel : Nat := 100000

def main (args : List String) : IO Unit := do
  match args with
  | ["check", path] =>
    -- say where the program may fail
    let src ← IO.FS.readFile path
    match parse src with
    | .ok ast =>
      let msgs := Report.report ([] : AbsInt.AEnv AbsInt.Itv) ast
      for m in msgs do IO.println m
    | .error e =>
      IO.eprintln s!"parse error: {e}"
      IO.Process.exit 1
  | [path] =>
    let src ← IO.FS.readFile path
    match parse src with
    | .ok ast  =>
      IO.println (toString ast)
      match eval fuel [] [] ast with
      | .ok v _ => IO.println s!"= {v}"
      | .err k _ =>
        IO.eprintln s!"runtime error: {ppErr k}"
        IO.Process.exit 1
      | .outOfFuel =>
        IO.eprintln "out of fuel"
        IO.Process.exit 1
    | .error e =>
      IO.eprintln s!"parse error: {e}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "usage: diva <file>  or  diva check <file>"
    IO.Process.exit 1
