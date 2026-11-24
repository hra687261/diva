import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let clamp x = ...`, with its contract. -/
def clamp_fn : RecFun where
  name := "clamp"
  f := none
  x := "x"
  body := (.ite (.binop .lt (.var "x") (.int 0)) (.int 0) (.ite (.binop .gt (.var "x") (.int 100)) (.int 100) (.var "x")))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ x : Int, arg₀ = .int x ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ x r : Int, arg₀ = .int x ∧ res₀ = .int r ∧
        ((r ≥ 0) ∧ (r ≤ 100))
      | _, _ => False }

/-- The proof obligation of `clamp`. If the proof fails, write one by hand. -/
theorem clamp_body : clamp_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [clamp_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `clamp` meets its contract: every call of `clamp` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem clamp_correct : clamp_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, clamp_body⟩

/-- The obligation of the top-level expression `(clamp 150)`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [clamp_fn] (.app (.var "clamp") (.int 150)) (fun _ _ => True) [("clamp", clamp_fn.clos)] μ := by
  simp [clamp_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(clamp 150)` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.app (.var "clamp") (.int 150)) (fun _ _ => True) [("clamp", clamp_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [clamp_fn]) ⟨trivial, clamp_body⟩ (top1_wp μ)
