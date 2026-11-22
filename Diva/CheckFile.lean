import Lean

/-!
# Checking a Lean file inside `diva`

`run` checks a Lean file the way the command `lean` does, but inside `diva`. So `diva`
also gets the environment of the checked file: the theorems that Lean accepted. Then
`run` checks the axioms that each theorem uses. A proof with `sorry` uses the axiom
`sorryAx`, and Lean only prints a warning for it. `run` reports it as an error.

Importing the same modules a second time in the same process gives an environment
without them. So `imported` imports each list of modules once, and keeps the result.

TODO: each check runs Lean on the whole file again, even if only one proof changed.
This is not ideal and could get slow on large files.
TODO: investigate bisection of lean files (selecting only the subsets that are
sufficient for checking the proof)
-/

namespace Diva.CheckFile

open Lean Elab

/-- The axioms that a proof may use. `native_decide` and `decide +native` use other
    axioms, such as `Lean.ofReduceBool`. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The environments imported so far, with the list of modules of each one. -/
initialize importedRef : IO.Ref (List (Array Import × Environment)) ← IO.mkRef []

/-- The environment of the modules `imports`. They are imported only the first time.
    The modules must be in Lean's search path. -/
def imported (imports : Array Import) : IO Environment := do
  if let some (_, env) := (← importedRef.get).find? (·.1 == imports) then return env
  let env ← importModules imports {} (loadExts := true)
  importedRef.modify ((imports, env) :: ·)
  return env

/-- The environment of the modules that the file `input` imports (its `import` lines),
    with the parser state after these lines. -/
def header (inputCtx : Parser.InputContext) :
    IO (Environment × Parser.ModuleParserState) := do
  let (header, parserState, _) ← Parser.parseHeader inputCtx
  return (← imported (HeaderSyntax.imports header), parserState)

/-- The environment and Lean's messages after Lean checks the file `input`, named
    `fileName`. -/
def elabFile (fileName input : String) : IO (Environment × MessageLog) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (env, parserState) ← header inputCtx
  let s ← IO.processCommands inputCtx parserState (Command.mkState env {} {})
  return (s.commandState.env, s.commandState.messages)

/-- `collectAxioms` needs a monad that holds an environment. -/
instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

/-- The axioms that the theorem `n` uses, other than `standardAxioms`. -/
def otherAxioms (env : Environment) (n : Name) : List Name :=
  ((collectAxioms n : StateM Environment _).run' env).toList.filter
    (!standardAxioms.contains ·)

/-- An error, in Lean's format `file:line:col: error: ...`, for each theorem of `input`
    that uses other axioms than `standardAxioms`. A theorem is found by its line
    `theorem name ...`. -/
def axiomErrors (env : Environment) (fileName input : String) : List String :=
  (input.splitOn "\n").zipIdx.filterMap fun (l, i) =>
    if !l.startsWith "theorem " then none
    else
      let name := ((l.drop 8).toString.splitOn " ").headD ""
      match otherAxioms env name.toName with
      | [] => none
      | axs => some s!"{fileName}:{i + 1}:0: error: `{name}` uses the axioms {axs}, so it isn't proved"

/-- Check the file `input`, named `fileName`, with Lean. If Lean accepts it, and its
    theorems use only `standardAxioms`, the result is `none`. Otherwise it is
    `some errors`, where `errors` are Lean's errors, or the errors of `axiomErrors`.
    The axioms are checked only if Lean has no error. -/
def run (fileName input : String) : IO (Option String) := do
  let (env, messages) ← elabFile fileName input
  let errors ← messages.toList.filter (·.severity == .error) |>.mapM (·.toString)
  if !errors.isEmpty then return some (String.join errors)
  match axiomErrors env fileName input with
  | [] => return none
  | errs => return some ("\n".intercalate errs ++ "\n")

end Diva.CheckFile
