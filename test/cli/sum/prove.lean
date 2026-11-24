import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let rec sum n = ...`, with its contract. -/
def sum_fn : RecFun where
  name := "sum"
  f := some "sum"
  x := "n"
  body := (.ite (.binop .le (.var "n") (.int 0)) (.int 0) (.binop .add (.var "n") (.app (.var "sum") (.binop .sub (.var "n") (.int 1)))))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ n : Int, arg₀ = .int n ∧ (n ≥ 0)
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ n r : Int, arg₀ = .int n ∧ res₀ = .int r ∧
        ((r ≥ 0) ∧ (r ≥ n))
      | _, _ => False }

/-- The proof obligation of `sum`. If the proof fails, write one by hand. -/
theorem sum_body : sum_fn.BodyOk .none [] := by
  intro va μ ⟨n, hva, hpre⟩
  subst hva
  simp [sum_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `sum` meets its contract: every call of `sum` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem sum_correct : sum_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, sum_body⟩

/-- The obligation of the top-level expression `(sum 10)`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [sum_fn] (.app (.var "sum") (.int 10)) (fun _ _ => True) [("sum", sum_fn.clos)] μ := by
  simp [sum_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(sum 10)` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.app (.var "sum") (.int 10)) (fun _ _ => True) [("sum", sum_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [sum_fn]) ⟨trivial, sum_body⟩ (top1_wp μ)
