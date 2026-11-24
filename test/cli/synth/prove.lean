import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let abs x = ...`, with its contract. -/
def abs_fn : RecFun where
  f := none
  x := "x"
  body := (.ite (.binop .lt (.var "x") (.int 0)) (.binop .sub (.int 0) (.var "x")) (.var "x"))
  ρ := []
  spec := {
    pre := fun arg₀ => ∃ x : Int, arg₀ = .int x ∧ True
    post := fun arg₀ res₀ => ∃ x r : Int, arg₀ = .int x ∧ res₀ = .int r ∧
      ((r ≥ 0) ∧ ((r ≥ x) ∧ (r ≥ (0 - x)))) }

/-- The proof obligation of `abs`. If the proof fails, write one by hand. -/
theorem abs_body : abs_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [abs_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `abs` meets its contract: every call of `abs` on an argument that satisfies
    `requires` gives a result that satisfies `ensures`. -/
theorem abs_correct : abs_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, abs_body⟩
