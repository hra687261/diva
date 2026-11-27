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
      | [arg₀] => ∃ (x : Int), arg₀ = .int x ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (x : Int) (r : Int), arg₀ = .int x ∧ res₀ = .int r ∧
        ((r ≥ 0) ∧ ((r ≥ x) ∧ (r ≥ (0 - x))))
      | _, _ => False }

/-- The proof obligation of `abs`. If the proof fails, write one by hand. -/
theorem abs_body : abs_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [abs_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `abs` meets its contract: every call of `abs` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem abs_correct : abs_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, abs_body⟩

/-- `let dist a = ...`, with its contract. -/
def dist_fn : RecFun where
  name := "dist"
  f := none
  x := "a"
  body := (.app (.var "abs") (.binop .sub (.var "a") (.int 10)))
  ρ := [("abs", abs_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ (a : Int), arg₀ = .int a ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (a : Int) (result : Int), arg₀ = .int a ∧ res₀ = .int result ∧
        (result ≥ 0)
      | _, _ => False }

/-- The proof obligation of `dist`. If the proof fails, write one by hand. -/
theorem dist_body : dist_fn.BodyOk .none [abs_fn] := by
  intro va μ ⟨a, hva, hpre⟩
  subst hva
  simp [dist_fn, abs_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `dist` meets its contract: every call of `dist` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem dist_correct : dist_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [abs_fn]) ⟨⟨trivial, abs_body⟩, dist_body⟩

/-- The obligation of the top-level expression `(dist 3)`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [dist_fn, abs_fn] (.app (.var "dist") (.int 3)) (fun _ _ => True) [("dist", dist_fn.clos), ("abs", abs_fn.clos)] μ := by
  simp [dist_fn, abs_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(dist 3)` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.app (.var "dist") (.int 3)) (fun _ _ => True) [("dist", dist_fn.clos), ("abs", abs_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [dist_fn, abs_fn]) ⟨⟨trivial, abs_body⟩, dist_body⟩ (top1_wp μ)
