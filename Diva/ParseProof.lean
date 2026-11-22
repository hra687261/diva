import Lean

/-!
# Checking a proof from an LLM with Lean's parser

`diva prove` writes a proof from an LLM after `:= by`. Before that, `check` parses
the proof with Lean's parser, in the environment of the file (`Diva.Wp` and the
tactics it has). The proof must be only tactics, so it can't end the `by` block and
add commands to the file, such as a `def` that changes what a theorem states. Then
`check` looks for the keywords of `forbidden` in the parsed proof.

TODO: this might be too strict, have better rejection criteria.
-/

namespace Diva.ParseProof

open Lean

/-- The keywords and names that a proof from the oracle can't contain. Each one could
    make Lean accept a false theorem, or run code.

    TODO: investigate if it would not be better to have a list of allowed tacticts
    Ideally we'd like to be as expressive as possible without making mistakes.
    -/
def forbidden : Std.HashSet String := Std.HashSet.ofList
  ["sorry", "admit", "stop", "native_decide",
    -- prove any goal, or trust compiled code instead of the kernel. The axiom check
    -- (`#only_standard_axioms`) catches them too, but only after running Lean.
   "set_option",
    -- could turn off checks, such as `debug.skipKernelTC`
   "run_tac", "by_elab", "unsafe"]
    -- run code while Lean checks the file

/-- The keywords and the parts of the names in `stx`. `Lean.Elab.foo` gives `Lean`,
    `Elab` and `foo`. Comments and strings are not in `stx`, so they are not checked. -/
partial def words : Syntax → List String
  | .atom _ s => [s]
  | .ident _ _ n _ => n.components.map toString
  | .node _ _ args => args.toList.flatMap words
  | .missing => []

/-- Why the proof `proof` (tactics, one per line) can't be used, or `none` if it can.
    It is parsed as it is written in the file: after `by`, with each line indented
    by 2 spaces. `env` gives the tactics that the parser knows. -/
def check (env : Environment) (proof : String) : Option String :=
  let text := "by\n" ++ "\n".intercalate ((proof.splitOn "\n").map ("  " ++ ·))
  match Parser.runParserCategory env `term text "<proof>" with
  | .error msg => some s!"it isn't only tactics: {msg}"
  | .ok stx => ((words stx).find? forbidden.contains).map (s!"it uses `{·}`")

end Diva.ParseProof
