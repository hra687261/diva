import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let pick b x y = ...`, with its contract. -/
def pick_fn : RecFun where
  name := "pick"
  f := none
  x := "b"
  rest := ["x", "y"]
  body := (.ite (.var "b") (.var "x") (.var "y"))
  ρ := []
  spec := {
    pre := fun
      | [arg₀, arg₁, arg₂] => ∃ (b : Bool) (x : Int) (y : Int), arg₀ = .bool b ∧ arg₁ = .int x ∧ arg₂ = .int y ∧ ((b = true) ∨ (x = y))
      | _ => False
    post := fun
      | [arg₀, arg₁, arg₂], res₀ => ∃ (b : Bool) (x : Int) (y : Int) (r : Int), arg₀ = .bool b ∧ arg₁ = .int x ∧ arg₂ = .int y ∧ res₀ = .int r ∧
        (r = x)
      | _, _ => False }

/-- The proof obligation of `pick`. If the proof fails, write one by hand. -/
theorem pick_body : pick_fn.BodyOk .none [] := by
  intro va₀ va₁ va₂ μ ⟨b, x, y, hva₀, hva₁, hva₂, hpre⟩
  subst hva₀ hva₁ hva₂
  cases b
  all_goals simp [pick_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos] at *
  all_goals split_omega

/-- `pick` meets its contract: every call of `pick` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem pick_correct : pick_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, pick_body⟩

/-- `let negate b = ...`, with its contract. -/
def negate_fn : RecFun where
  name := "negate"
  f := none
  x := "b"
  body := (.ite (.var "b") (.bool false) (.bool true))
  ρ := [("pick", pick_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ (b : Bool), arg₀ = .bool b ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (b : Bool) (r : Bool), arg₀ = .bool b ∧ res₀ = .bool r ∧
        ((r = true) ↔ (¬ (b = true)))
      | _, _ => False }

/-- The proof obligation of `negate`. If the proof fails, write one by hand. -/
theorem negate_body : negate_fn.BodyOk .none [pick_fn] := by
  intro va μ ⟨b, hva, hpre⟩
  subst hva
  cases b
  all_goals simp [negate_fn, pick_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos] at *
  all_goals split_omega

/-- `negate` meets its contract: every call of `negate` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem negate_correct : negate_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [pick_fn]) ⟨⟨trivial, pick_body⟩, negate_body⟩

/-- `let is_empty l = ...`, with its contract. -/
def is_empty_fn : RecFun where
  name := "is_empty"
  f := none
  x := "l"
  body := (.matchList (.var "l") (.bool true) "_" "_" (.bool false))
  ρ := [("negate", negate_fn.clos), ("pick", pick_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ (l : Diva.Value), arg₀ = l ∧ l.isProperList = true ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (l : Diva.Value) (r : Bool), arg₀ = l ∧ l.isProperList = true ∧ res₀ = .bool r ∧
        ((r = true) ↔ ((Diva.Value.length l) = 0))
      | _, _ => False }

/-- The proof obligation of `is_empty`. If the proof fails, write one by hand. -/
theorem is_empty_body : is_empty_fn.BodyOk .none [negate_fn, pick_fn] := by
  intro va μ ⟨l, hva, hpre⟩
  subst hva
  cases va
  all_goals simp [is_empty_fn, negate_fn, pick_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos] at *
  all_goals split_lists

/-- `is_empty` meets its contract: every call of `is_empty` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem is_empty_correct : is_empty_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [negate_fn, pick_fn]) ⟨⟨⟨trivial, pick_body⟩, negate_body⟩, is_empty_body⟩

/-- `let at_least_two l = ...`, with its contract. -/
def at_least_two_fn : RecFun where
  name := "at_least_two"
  f := none
  x := "l"
  body := (.matchList (.var "l") (.int 0) "_" "t" (.matchList (.var "t") (.int 1) "_" "_" (.int 2)))
  ρ := [("is_empty", is_empty_fn.clos), ("negate", negate_fn.clos), ("pick", pick_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ (l : Diva.Value), arg₀ = l ∧ l.isProperList = true ∧ ((Diva.Value.length l) ≥ 2)
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (l : Diva.Value) (r : Int), arg₀ = l ∧ l.isProperList = true ∧ res₀ = .int r ∧
        (r = 2)
      | _, _ => False }

/-- The proof obligation of `at_least_two`. If the proof fails, write one by hand. -/
theorem at_least_two_body : at_least_two_fn.BodyOk .none [is_empty_fn, negate_fn, pick_fn] := by
  intro va μ ⟨l, hva, hpre⟩
  subst hva
  cases va
  all_goals simp [at_least_two_fn, is_empty_fn, negate_fn, pick_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos] at *
  all_goals split_lists

/-- `at_least_two` meets its contract: every call of `at_least_two` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem at_least_two_correct : at_least_two_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [is_empty_fn, negate_fn, pick_fn]) ⟨⟨⟨⟨trivial, pick_body⟩, negate_body⟩, is_empty_body⟩, at_least_two_body⟩

/-- The obligation of the top-level expression `(((((pick (negate false)) 1) 2) + (at_least_two (3 :: (4 :: [])))) + (if (is_empty []) then 1 else 0))`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [at_least_two_fn, is_empty_fn, negate_fn, pick_fn] (.binop .add (.binop .add (.app (.app (.app (.var "pick") (.app (.var "negate") (.bool false))) (.int 1)) (.int 2)) (.app (.var "at_least_two") (.cons (.int 3) (.cons (.int 4) .nil)))) (.ite (.app (.var "is_empty") .nil) (.int 1) (.int 0))) (fun _ _ => True) [("at_least_two", at_least_two_fn.clos), ("is_empty", is_empty_fn.clos), ("negate", negate_fn.clos), ("pick", pick_fn.clos)] μ := by
  simp [at_least_two_fn, is_empty_fn, negate_fn, pick_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(((((pick (negate false)) 1) 2) + (at_least_two (3 :: (4 :: [])))) + (if (is_empty []) then 1 else 0))` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.binop .add (.binop .add (.app (.app (.app (.var "pick") (.app (.var "negate") (.bool false))) (.int 1)) (.int 2)) (.app (.var "at_least_two") (.cons (.int 3) (.cons (.int 4) .nil)))) (.ite (.app (.var "is_empty") .nil) (.int 1) (.int 0))) (fun _ _ => True) [("at_least_two", at_least_two_fn.clos), ("is_empty", is_empty_fn.clos), ("negate", negate_fn.clos), ("pick", pick_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [at_least_two_fn, is_empty_fn, negate_fn, pick_fn]) ⟨⟨⟨⟨trivial, pick_body⟩, negate_body⟩, is_empty_body⟩, at_least_two_body⟩ (top1_wp μ)
