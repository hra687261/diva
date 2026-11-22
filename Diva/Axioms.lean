import Lean

/-!
# Checking the axioms of a theorem

`#only_standard_axioms t` fails if the theorem `t` depends on an axiom other than the three
standard ones (`propext`, `Classical.choice` and `Quot.sound`). For example, a proof
with `sorry` uses the axiom `sorryAx`, and `native_decide` uses `Lean.ofReduceBool`.
For `sorry`, Lean only prints a warning. With `#only_standard_axioms`, it reports an error.
-/

namespace Diva

open Lean Elab Command

/-- The axioms that a proof may use. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether the proof of `n`, or of a declaration of this file that it uses, failed.
    Lean replaces a proof that fails by a `sorry` that it marks as synthetic, and
    reports an error for it. `seen` are the declarations visited so far. The imported
    declarations are skipped, because they were checked when their file was built. -/
partial def failedProof (env : Environment) (n : Name) : StateM NameSet Bool := do
  if (← get).contains n then return false
  modify (·.insert n)
  if (env.getModuleIdxFor? n).isSome then return false
  let some v := (env.find? n).bind (·.value? (allowOpaque := true)) | return false
  if v.hasSyntheticSorry then return true
  v.getUsedConstants.anyM (failedProof env)

/-- `#only_standard_axioms t`: an error if the theorem `t` depends on an axiom that is not in
    `standardAxioms`. If a proof that `t` uses failed, Lean already reported an error, so
    there is no other error. -/
elab "#only_standard_axioms " t:ident : command => do
  let name ← liftCoreM (realizeGlobalConstNoOverloadWithInfo t)
  if ((failedProof (← getEnv) name).run' {}).run then return
  let others := (← collectAxioms name).toList.filter (!standardAxioms.contains ·)
  unless others.isEmpty do
    throwError "`{name}` depends on the axioms {others}, so it isn't proved"

end Diva
