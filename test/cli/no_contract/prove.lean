import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let half x = ...`, without a contract: it gets the empty contract. Its proof
    says that `half` doesn't fail on integers. -/
def half_fn : RecFun where
  name := "half"
  f := none
  x := "x"
  body := (.binop .div (.var "x") (.int 2))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ x : Int, arg₀ = .int x ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ x result : Int, arg₀ = .int x ∧ res₀ = .int result ∧
        True
      | _, _ => False }

/-- The proof obligation of `half`. If the proof fails, write one by hand. -/
theorem half_body : half_fn.BodyOk .none [] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [half_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `half` meets its contract: every call of `half` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem half_correct : half_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, half_body⟩

/-- `let inv x = ...`, without a contract: it gets the empty contract. Its proof
    says that `inv` doesn't fail on integers. -/
def inv_fn : RecFun where
  name := "inv"
  f := none
  x := "x"
  body := (.binop .div (.int 100) (.var "x"))
  ρ := [("half", half_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ x : Int, arg₀ = .int x ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ x result : Int, arg₀ = .int x ∧ res₀ = .int result ∧
        True
      | _, _ => False }

/-- The proof obligation of `inv`. If the proof fails, write one by hand. -/
theorem inv_body : inv_fn.BodyOk .none [half_fn] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [inv_fn, half_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `inv` meets its contract: every call of `inv` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem inv_correct : inv_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [half_fn]) ⟨⟨trivial, half_body⟩, inv_body⟩

/-- `unused`, which has no contract. -/
def unused_val : Value := .clos none "x" (.binop .div (.int 1) (.int 0)) [("inv", inv_fn.clos), ("half", half_fn.clos)]

/-- `let f x = ...`, with its contract. -/
def f_fn : RecFun where
  name := "f"
  f := none
  x := "x"
  body := (.binop .add (.app (.var "half") (.var "x")) (.app (.var "inv") (.var "x")))
  ρ := [("unused", unused_val), ("inv", inv_fn.clos), ("half", half_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ x : Int, arg₀ = .int x ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ x r : Int, arg₀ = .int x ∧ res₀ = .int r ∧
        True
      | _, _ => False }

/-- The proof obligation of `f`. If the proof fails, write one by hand. -/
theorem f_body : f_fn.BodyOk .none [inv_fn, half_fn] := by
  intro va μ ⟨x, hva, hpre⟩
  subst hva
  simp [f_fn, unused_val, inv_fn, half_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `f` meets its contract: every call of `f` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem f_correct : f_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [inv_fn, half_fn]) ⟨⟨⟨trivial, half_body⟩, inv_body⟩, f_body⟩
