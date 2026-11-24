import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let max a b = ...`, with its contract. -/
def max_fn : RecFun where
  name := "max"
  f := none
  x := "a"
  rest := ["b"]
  body := (.ite (.binop .lt (.var "a") (.var "b")) (.var "b") (.var "a"))
  ρ := []
  spec := {
    pre := fun
      | [arg₀, arg₁] => ∃ a b : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ True
      | _ => False
    post := fun
      | [arg₀, arg₁], res₀ => ∃ a b r : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ res₀ = .int r ∧
        ((r ≥ a) ∧ (r ≥ b))
      | _, _ => False }

/-- The proof obligation of `max`. If the proof fails, write one by hand. -/
theorem max_body : max_fn.BodyOk .none [] := by
  intro va₀ va₁ μ ⟨a, b, hva₀, hva₁, hpre⟩
  subst hva₀ hva₁
  simp [max_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `max` meets its contract: every call of `max` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem max_correct : max_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, max_body⟩
