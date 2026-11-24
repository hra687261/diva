import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let abs x = ...`, with its contract. -/
def abs_fn : RecFun where
  name := "abs"
  f := none
  x := "x"
  body := (.ite (.binop .lt (.var "x") (.int 0)) (.binop .sub (.int 0) (.var "x")) (.var "x"))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ x : Int, arg₀ = .int x ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ x r : Int, arg₀ = .int x ∧ res₀ = .int r ∧
        ((r ≥ 0) ∧ ((r ≥ x) ∧ (r ≥ (0 - x))))
      | _, _ => False }

/-- The proof obligation of `abs`. If the proof fails, write one by hand. -/
theorem abs_body : abs_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [abs_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `abs` meets its contract: every call of `abs` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem abs_correct : abs_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, abs_body⟩

/-- The obligation of the top-level expression `(abs (0 - 7))`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [abs_fn] (.app (.var "abs") (.binop .sub (.int 0) (.int 7))) (fun _ _ => True) [("abs", abs_fn.clos)] μ := by
  simp [abs_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(abs (0 - 7))` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.app (.var "abs") (.binop .sub (.int 0) (.int 7))) (fun _ _ => True) [("abs", abs_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [abs_fn]) ⟨trivial, abs_body⟩ (top1_wp μ)
