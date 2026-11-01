import Diva

open Diva

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let src ← IO.FS.readFile path
    match parse src with
    | .ok ast  => IO.println (toString ast)
    | .error e =>
      IO.eprintln s!"parse error: {e}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "usage: diva <file>"
    IO.Process.exit 1
