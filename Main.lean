import Diva

open Diva

/-- Evaluation fuel bound. -/
def fuel : Nat := 100000

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let src ← IO.FS.readFile path
    match parse src with
    | .ok ast  =>
      IO.println (toString ast)
      match eval fuel [] ast with
      | some v => IO.println s!"= {v}"
      | none =>
        IO.eprintln "evaluation stuck or out of fuel"
        IO.Process.exit 1
    | .error e =>
      IO.eprintln s!"parse error: {e}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "usage: diva <file>"
    IO.Process.exit 1
