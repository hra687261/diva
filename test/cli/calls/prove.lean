import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let double x = ...`, with its contract. -/
def double_fn : RecFun where
  name := "double"
  f := none
  x := "x"
  body := (.binop .add (.var "x") (.var "x"))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ (x : Int), arg₀ = .int x ∧ (x ≥ 0)
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (x : Int) (r : Int), arg₀ = .int x ∧ res₀ = .int r ∧
        (r ≥ 0)
      | _, _ => False }

/-- The proof obligation of `double`. If the proof fails, write one by hand. -/
theorem double_body : double_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [double_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `double` meets its contract: every call of `double` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem double_correct : double_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, double_body⟩

/-- `let quad x = ...`, with its contract. -/
def quad_fn : RecFun where
  name := "quad"
  f := none
  x := "x"
  body := (.app (.var "double") (.app (.var "double") (.var "x")))
  ρ := [("double", double_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ (x : Int), arg₀ = .int x ∧ (x ≥ 0)
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (x : Int) (r : Int), arg₀ = .int x ∧ res₀ = .int r ∧
        (r ≥ 0)
      | _, _ => False }

/-- The proof obligation of `quad`. If the proof fails, write one by hand. -/
theorem quad_body : quad_fn.BodyOk .none [double_fn] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [quad_fn, double_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `quad` meets its contract: every call of `quad` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem quad_correct : quad_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [double_fn]) ⟨⟨trivial, double_body⟩, quad_body⟩

/-- The obligation of the top-level expression `(quad 3)`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [quad_fn, double_fn] (.app (.var "quad") (.int 3)) (fun _ _ => True) [("quad", quad_fn.clos), ("double", double_fn.clos)] μ := by
  simp [quad_fn, double_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(quad 3)` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.app (.var "quad") (.int 3)) (fun _ _ => True) [("quad", quad_fn.clos), ("double", double_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [quad_fn, double_fn]) ⟨⟨trivial, double_body⟩, quad_body⟩ (top1_wp μ)
