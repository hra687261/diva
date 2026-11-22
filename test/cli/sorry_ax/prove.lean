import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let square x = ...`, with its contract. -/
def square_fn : RecFun where
  f := none
  x := "x"
  body := (.binop .mul (.var "x") (.var "x"))
  ρ := []
  spec := {
    pre := fun arg₀ => ∃ x : Int, arg₀ = .int x ∧ True
    post := fun arg₀ res₀ => ∃ x r : Int, arg₀ = .int x ∧ res₀ = .int r ∧
      (r ≥ 0) }

/-- The proof obligation of `square`. If the proof fails, write one by hand. -/
theorem square_body : square_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [square_fn, wp, BinOp.denote, List.lookup, callEnv]
  exact sorryAx _ false

/-- `square` meets its contract: every call of `square` on an argument that satisfies
    `requires` gives a result that satisfies `ensures`. -/
theorem square_correct : square_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, square_body⟩
