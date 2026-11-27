import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let square x = ...`, with its contract. -/
def square_fn : RecFun where
  name := "square"
  f := none
  x := "x"
  body := (.binop .mul (.var "x") (.var "x"))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ (x : Int), arg₀ = .int x ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (x : Int) (r : Int), arg₀ = .int x ∧ res₀ = .int r ∧
        (r ≥ 0)
      | _, _ => False }

/-- The proof obligation of `square`. If the proof fails, write one by hand. -/
theorem square_body : square_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [square_fn, wp, BinOp.denote, List.lookup, callEnv]
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h h

/-- `square` meets its contract: every call of `square` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem square_correct : square_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, square_body⟩

/-- The obligation of the top-level expression `(square 3)`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [square_fn] (.app (.var "square") (.int 3)) (fun _ _ => True) [("square", square_fn.clos)] μ := by
  simp [square_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(square 3)` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.app (.var "square") (.int 3)) (fun _ _ => True) [("square", square_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [square_fn]) ⟨trivial, square_body⟩ (top1_wp μ)
