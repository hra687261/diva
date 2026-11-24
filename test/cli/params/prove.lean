import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let rec mul a b = ...`, with its contract. -/
def mul_fn : RecFun where
  name := "mul"
  f := some "mul"
  x := "a"
  rest := ["b"]
  body := (.ite (.binop .le (.var "b") (.int 0)) (.int 0) (.binop .add (.var "a") (.app (.app (.var "mul") (.var "a")) (.binop .sub (.var "b") (.int 1)))))
  ρ := []
  spec := {
    pre := fun
      | [arg₀, arg₁] => ∃ a b : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ (a ≥ 0)
      | _ => False
    post := fun
      | [arg₀, arg₁], res₀ => ∃ a b r : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ res₀ = .int r ∧
        (r ≥ 0)
      | _, _ => False }

/-- The proof obligation of `mul`. If the proof fails, write one by hand. -/
theorem mul_body : mul_fn.BodyOk .none [] := by
  intro va₀ va₁ μ ⟨a, b, hva₀, hva₁, hpre⟩
  subst hva₀ hva₁
  simp [mul_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `mul` meets its contract: every call of `mul` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem mul_correct : mul_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, mul_body⟩

/-- `let max a b = ...`, with its contract. -/
def max_fn : RecFun where
  name := "max"
  f := none
  x := "a"
  rest := ["b"]
  body := (.ite (.binop .lt (.var "a") (.var "b")) (.var "b") (.var "a"))
  ρ := [("mul", mul_fn.clos)]
  spec := {
    pre := fun
      | [arg₀, arg₁] => ∃ a b : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ True
      | _ => False
    post := fun
      | [arg₀, arg₁], res₀ => ∃ a b r : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ res₀ = .int r ∧
        ((r ≥ a) ∧ (r ≥ b))
      | _, _ => False }

/-- The proof obligation of `max`. If the proof fails, write one by hand. -/
theorem max_body : max_fn.BodyOk .none [mul_fn] := by
  intro va₀ va₁ μ ⟨a, b, hva₀, hva₁, hpre⟩
  subst hva₀ hva₁
  simp [max_fn, mul_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `max` meets its contract: every call of `max` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem max_correct : max_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [mul_fn]) ⟨⟨trivial, mul_body⟩, max_body⟩

/-- `let max3 a b c = ...`, with its contract. -/
def max3_fn : RecFun where
  name := "max3"
  f := none
  x := "a"
  rest := ["b", "c"]
  body := (.app (.app (.var "max") (.app (.app (.var "max") (.var "a")) (.var "b"))) (.var "c"))
  ρ := [("max", max_fn.clos), ("mul", mul_fn.clos)]
  spec := {
    pre := fun
      | [arg₀, arg₁, arg₂] => ∃ a b c : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ arg₂ = .int c ∧ True
      | _ => False
    post := fun
      | [arg₀, arg₁, arg₂], res₀ => ∃ a b c r : Int, arg₀ = .int a ∧ arg₁ = .int b ∧ arg₂ = .int c ∧ res₀ = .int r ∧
        ((r ≥ a) ∧ ((r ≥ b) ∧ (r ≥ c)))
      | _, _ => False }

/-- The proof obligation of `max3`. If the proof fails, write one by hand. -/
theorem max3_body : max3_fn.BodyOk .none [max_fn, mul_fn] := by
  intro va₀ va₁ va₂ μ ⟨a, b, c, hva₀, hva₁, hva₂, hpre⟩
  subst hva₀ hva₁ hva₂
  simp [max3_fn, max_fn, mul_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `max3` meets its contract: every call of `max3` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem max3_correct : max3_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [max_fn, mul_fn]) ⟨⟨⟨trivial, mul_body⟩, max_body⟩, max3_body⟩

/-- `let area w h = ...`, with its contract. -/
def area_fn : RecFun where
  name := "area"
  f := none
  x := "w"
  rest := ["h"]
  body := (.app (.app (.var "mul") (.app (.app (.var "max") (.var "w")) (.int 0))) (.var "h"))
  ρ := [("max3", max3_fn.clos), ("max", max_fn.clos), ("mul", mul_fn.clos)]
  spec := {
    pre := fun
      | [arg₀, arg₁] => ∃ w h : Int, arg₀ = .int w ∧ arg₁ = .int h ∧ True
      | _ => False
    post := fun
      | [arg₀, arg₁], res₀ => ∃ w h r : Int, arg₀ = .int w ∧ arg₁ = .int h ∧ res₀ = .int r ∧
        (r ≥ 0)
      | _, _ => False }

/-- The proof obligation of `area`. If the proof fails, write one by hand. -/
theorem area_body : area_fn.BodyOk .none [max3_fn, max_fn, mul_fn] := by
  intro va₀ va₁ μ ⟨w, h, hva₀, hva₁, hpre⟩
  subst hva₀ hva₁
  simp [area_fn, max3_fn, max_fn, mul_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `area` meets its contract: every call of `area` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem area_correct : area_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [max3_fn, max_fn, mul_fn]) ⟨⟨⟨⟨trivial, mul_body⟩, max_body⟩, max3_body⟩, area_body⟩
