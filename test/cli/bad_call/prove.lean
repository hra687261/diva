import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let inv x = ...`, with its contract. -/
def inv_fn : RecFun where
  name := "inv"
  f := none
  x := "x"
  body := (.binop .div (.int 100) (.var "x"))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ x : Int, arg₀ = .int x ∧ (x ≠ 0)
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ x r : Int, arg₀ = .int x ∧ res₀ = .int r ∧
        True
      | _, _ => False }

/-- The proof obligation of `inv`. If the proof fails, write one by hand. -/
theorem inv_body : inv_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [inv_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `inv` meets its contract: every call of `inv` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem inv_correct : inv_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, inv_body⟩

/-- The obligation of the top-level expression `(inv 0)`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [inv_fn] (.app (.var "inv") (.int 0)) (fun _ _ => True) [("inv", inv_fn.clos)] μ := by
  simp [inv_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(inv 0)` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.app (.var "inv") (.int 0)) (fun _ _ => True) [("inv", inv_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [inv_fn]) ⟨trivial, inv_body⟩ (top1_wp μ)
