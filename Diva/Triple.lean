import Diva.Semantics

/-!
# Contracts as triples, and their proof rules

`Triple P e Q` (a Hoare triple): every run of `e` that starts where the precondition
`P` holds gives a value, and the postcondition `Q` holds for it. Runs that never end
are not covered (partial correctness).

Hoare logic usually has one proof rule per construct. Here they are not separate
theorems. Each one is a case of the proof of `wp_sound` (`Wp.lean`).
Only the rule of consequence is stated below: if `P' → P`, `Triple P e Q` and
`Q → Q'`, then `Triple P' e Q'`.
-/

namespace Diva

/-- A precondition: a property of the environment and the store before a run. -/
abbrev Pre := Env → Store → Prop

/-- A postcondition: a property of the value and the store after a run. -/
abbrev Post := Value → Store → Prop

/-- Every run of `e` from `ρ` and `μ` gives a value `v`, and `Q` holds for `v` and
    the final store. -/
def Holds (e : Expr) (Q : Post) (ρ : Env) (μ : Store) : Prop :=
  ∀ r μ', Eval ρ μ e r μ' → ∃ v, r = .ok v ∧ Q v μ'

/-- `e` meets the contract `P`, `Q`: `Holds e Q` from every environment and store
    where `P` holds. -/
def Triple (P : Pre) (e : Expr) (Q : Post) : Prop :=
  ∀ ρ μ, P ρ μ → Holds e Q ρ μ

/-! ## The rule of consequence

A proved contract can be adapted: the precondition can ask for more, and the
postcondition can promise less. For example, `Triple (x ≥ 0) e (result > 0)` gives
`Triple (x ≥ 5) e (result ≥ 0)`. -/

/-- If `Q` holds after every run of `e`, and `Q` implies `Q'`, then `Q'` also holds. -/
theorem Holds.conseq {e : Expr} {Q Q' : Post} {ρ : Env} {μ : Store}
    (hQ : ∀ v μ, Q v μ → Q' v μ) (h : Holds e Q ρ μ) : Holds e Q' ρ μ := by
  intro r μ' he
  obtain ⟨v, hr, hq⟩ := h r μ' he
  exact ⟨v, hr, hQ v μ' hq⟩

/-- If `e` meets the contract `P`, `Q`, then `e` also meets `P'`, `Q'`, when `P'`
    implies `P` and `Q` implies `Q'`. -/
theorem Triple.conseq {P P' : Pre} {e : Expr} {Q Q' : Post}
    (hP : ∀ ρ μ, P' ρ μ → P ρ μ) (hQ : ∀ v μ, Q v μ → Q' v μ) (h : Triple P e Q) :
    Triple P' e Q' := by
  intro ρ μ hp
  exact (h ρ μ (hP ρ μ hp)).conseq hQ

end Diva
