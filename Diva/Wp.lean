import Diva.Triple

/-!
# Weakest preconditions

`wp e Q`: what must hold before `e` so that `Q` holds after (`wp_sound`). To prove
`Triple P e Q`, prove that `P` implies `wp e Q` (`triple_of_wp`). For integer
programs, `simp [wp]` then `omega` does it.

Covers literals, names, binop, `if`, `let` and `assert`. Other constructs give
`False`.
-/

namespace Diva

/-- The weakest precondition of `e` for the postcondition `Q`, from `ρ` and `μ`.
    Each case follows the proof rule of its construct (`Holds.binop`, ...). -/
def wp : Expr → Post → Env → Store → Prop
  | .int n, Q, _, μ => Q (.int n) μ
  | .bool b, Q, _, μ => Q (.bool b) μ
  | .unit, Q, _, μ => Q .unit μ
  | .var x, Q, ρ, μ => ∃ v, ρ.lookup x = some v ∧ Q v μ
  | .binop op a b, Q, ρ, μ =>
    wp a (fun va μ₁ => wp b (fun vb μ₂ => ∃ v, op.denote va vb = .ok v ∧ Q v μ₂) ρ μ₁) ρ μ
  | .ite c t e, Q, ρ, μ =>
    wp c (fun vc μ₁ => vc.isBool = true ∧
      (vc = .bool true → wp t Q ρ μ₁) ∧ (vc = .bool false → wp e Q ρ μ₁)) ρ μ
  | .letin x a b, Q, ρ, μ => wp a (fun v μ₁ => wp b Q ((x, v) :: ρ) μ₁) ρ μ
  | .assert c, Q, ρ, μ => wp c (fun vc μ₁ => vc = .bool true ∧ Q .unit μ₁) ρ μ
  | _, _, _, _ => False

/-- **`wp` is sound**: if `wp e Q ρ μ` holds, every run of `e` from `ρ` and `μ` gives
    a value that satisfies `Q`. -/
theorem wp_sound : ∀ (e : Expr) (Q : Post) (ρ : Env) (μ : Store),
    wp e Q ρ μ → Holds e Q ρ μ := by
  intro e
  induction e
  case int n =>
    intro Q ρ μ h
    exact Holds.int h
  case bool b =>
    intro Q ρ μ h
    exact Holds.bool h
  case unit =>
    intro Q ρ μ h
    exact Holds.unit h
  case var x =>
    intro Q ρ μ h
    obtain ⟨v, hx, hq⟩ := h
    exact Holds.var hx hq
  case binop op a b iha ihb =>
    intro Q ρ μ h
    apply Holds.binop
    apply (iha _ ρ μ h).conseq
    intro va μ₁ hb
    exact ihb _ ρ μ₁ hb
  case ite c t e ihc iht ihe =>
    intro Q ρ μ h
    apply Holds.ite
    apply (ihc _ ρ μ h).conseq
    intro vc μ₁ ⟨hb, hT, hF⟩
    exact ⟨hb, fun h => iht Q ρ μ₁ (hT h), fun h => ihe Q ρ μ₁ (hF h)⟩
  case letin x a b iha ihb =>
    intro Q ρ μ h
    apply Holds.letin
    apply (iha _ ρ μ h).conseq
    intro v μ₁ hb
    exact ihb Q _ μ₁ hb
  case assert c ihc =>
    intro Q ρ μ h
    exact Holds.assert (ihc _ ρ μ h)
  all_goals
    intro Q ρ μ h
    cases h

/-- `if c then .err k else .ok v` is `.ok w` exactly when `c` is false and `v = w`.
    `BinOp.denote .div` is `if y = 0 then .err .divZero else .ok ...`, so with this
    lemma `simp` turns "the division gives a value" into "the divisor isn't `0`". -/
@[simp] theorem ite_err_eq_ok {c : Prop} [Decidable c] {k : Err} {v w : Value} :
    ((if c then Outcome.err k else Outcome.ok v) = Outcome.ok w) ↔ (¬ c ∧ v = w) := by
  by_cases hc : c
  case pos => simp [hc]
  case neg => simp [hc]

/-- A contract holds if its precondition implies the weakest precondition. -/
theorem triple_of_wp {P : Pre} {e : Expr} {Q : Post}
    (h : ∀ ρ μ, P ρ μ → wp e Q ρ μ) : Triple P e Q := by
  intro ρ μ hp
  exact wp_sound e Q ρ μ (h ρ μ hp)

end Diva
