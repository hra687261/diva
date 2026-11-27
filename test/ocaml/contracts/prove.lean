import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let both a b = ...`, with its contract. -/
def both_fn : RecFun where
  name := "both"
  f := none
  x := "a"
  rest := ["b"]
  body := (.ite (.var "a") (.var "b") (.bool false))
  ρ := []
  spec := {
    pre := fun
      | [arg₀, arg₁] => ∃ (a : Bool) (b : Bool), arg₀ = .bool a ∧ arg₁ = .bool b ∧ True
      | _ => False
    post := fun
      | [arg₀, arg₁], res₀ => ∃ (a : Bool) (b : Bool) (r : Bool), arg₀ = .bool a ∧ arg₁ = .bool b ∧ res₀ = .bool r ∧
        ((r = true) ↔ ((a = true) ∧ (b = true)))
      | _, _ => False }

/-- The proof obligation of `both`. If the proof fails, write one by hand. -/
theorem both_body : both_fn.BodyOk .none [] := by
  intro va₀ va₁ μ ⟨a, b, hva₀, hva₁, hpre⟩
  subst hva₀ hva₁
  cases a
  cases b
  all_goals simp [both_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos] at *
  all_goals split_omega

/-- `both` meets its contract: every call of `both` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem both_correct : both_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, both_body⟩

/-- `let rec length l = ...`, with its contract. -/
def length_fn : RecFun where
  name := "length"
  f := some "length"
  x := "l"
  body := (.matchList (.var "l") (.int 0) "_" "t" (.letin "%r" (.binop .add (.int 1) (.app (.var "length") (.var "t"))) (.letin "_" (.assert (.ite (.binop .le (.int (-4611686018427387904)) (.var "%r")) (.binop .le (.var "%r") (.int 4611686018427387903)) (.bool false))) (.var "%r"))))
  ρ := [("both", both_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ (l : Diva.Value), arg₀ = l ∧ l.isProperList = true ∧ ((Diva.Value.length l) ≤ 100)
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (l : Diva.Value) (r : Int), arg₀ = l ∧ l.isProperList = true ∧ res₀ = .int r ∧
        (r = (Diva.Value.length l))
      | _, _ => False }

/-- The proof obligation of `length`. If the proof fails, write one by hand. -/
theorem length_body : length_fn.BodyOk .none [both_fn] := by
  intro va μ ⟨l, hva, hpre⟩
  subst hva
  cases va
  all_goals simp [length_fn, both_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos] at *
  all_goals split_lists

/-- `length` meets its contract: every call of `length` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem length_correct : length_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [both_fn]) ⟨⟨trivial, both_body⟩, length_body⟩

/-- `let has_two l = ...`, with its contract. -/
def has_two_fn : RecFun where
  name := "has_two"
  f := none
  x := "l"
  body := (.matchList (.var "l") (.bool false) "_" "%t1" (.matchList (.var "%t1") (.bool false) "_" "_" (.bool true)))
  ρ := [("length", length_fn.clos), ("both", both_fn.clos)]
  spec := {
    pre := fun
      | [arg₀] => ∃ (l : Diva.Value), arg₀ = l ∧ l.isProperList = true ∧ True
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (l : Diva.Value) (r : Bool), arg₀ = l ∧ l.isProperList = true ∧ res₀ = .bool r ∧
        ((r = true) ↔ ((Diva.Value.length l) ≥ 2))
      | _, _ => False }

/-- The proof obligation of `has_two`. If the proof fails, write one by hand. -/
theorem has_two_body : has_two_fn.BodyOk .none [length_fn, both_fn] := by
  intro va μ ⟨l, hva, hpre⟩
  subst hva
  cases va
  all_goals simp [has_two_fn, length_fn, both_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos] at *
  all_goals split_lists

/-- `has_two` meets its contract: every call of `has_two` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem has_two_correct : has_two_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := [length_fn, both_fn]) ⟨⟨⟨trivial, both_body⟩, length_body⟩, has_two_body⟩

/-- The obligation of the top-level expression `(if ((both true) (has_two (3 :: (4 :: [])))) then (let _ = (length (1 :: (2 :: []))) in ()) else ())`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [has_two_fn, length_fn, both_fn] (.ite (.app (.app (.var "both") (.bool true)) (.app (.var "has_two") (.cons (.int 3) (.cons (.int 4) .nil)))) (.letin "_" (.app (.var "length") (.cons (.int 1) (.cons (.int 2) .nil))) .unit) .unit) (fun _ _ => True) [("has_two", has_two_fn.clos), ("length", length_fn.clos), ("both", both_fn.clos)] μ := by
  simp [has_two_fn, length_fn, both_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(if ((both true) (has_two (3 :: (4 :: [])))) then (let _ = (length (1 :: (2 :: []))) in ()) else ())` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.ite (.app (.app (.var "both") (.bool true)) (.app (.var "has_two") (.cons (.int 3) (.cons (.int 4) .nil)))) (.letin "_" (.app (.var "length") (.cons (.int 1) (.cons (.int 2) .nil))) .unit) .unit) (fun _ _ => True) [("has_two", has_two_fn.clos), ("length", length_fn.clos), ("both", both_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [has_two_fn, length_fn, both_fn]) ⟨⟨⟨trivial, both_body⟩, length_body⟩, has_two_body⟩ (top1_wp μ)
