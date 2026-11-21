import Diva.Semantics

/-!
# Contracts as triples, and their proof rules

`Triple P e Q` (a Hoare triple): every run of `e` that starts where the precondition
`P` holds gives a value, and the postcondition `Q` holds for it. Runs that never end
are not covered (partial correctness).

The proof rules, one per construct, are proved once from `Eval`. Proofs of contracts
use them instead of cases on `Eval`.
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

/-! ## Proof rules -/

/-- The rule of consequence: a postcondition implied by `Q` also holds. -/
theorem Holds.conseq {e : Expr} {Q Q' : Post} {ρ : Env} {μ : Store}
    (hQ : ∀ v μ, Q v μ → Q' v μ) (h : Holds e Q ρ μ) : Holds e Q' ρ μ := by
  intro r μ' he
  obtain ⟨v, hr, hq⟩ := h r μ' he
  exact ⟨v, hr, hQ v μ' hq⟩

/-- The rule of consequence for triples: a stronger precondition, and a
    postcondition implied by `Q`. -/
theorem Triple.conseq {P P' : Pre} {e : Expr} {Q Q' : Post}
    (hP : ∀ ρ μ, P' ρ μ → P ρ μ) (hQ : ∀ v μ, Q v μ → Q' v μ) (h : Triple P e Q) :
    Triple P' e Q' := by
  intro ρ μ hp
  exact (h ρ μ (hP ρ μ hp)).conseq hQ

theorem Holds.int {n : Int} {Q : Post} {ρ : Env} {μ : Store} (h : Q (.int n) μ) :
    Holds (.int n) Q ρ μ := by
  intro r μ' he
  cases he
  exact ⟨_, rfl, h⟩

theorem Holds.bool {b : Bool} {Q : Post} {ρ : Env} {μ : Store} (h : Q (.bool b) μ) :
    Holds (.bool b) Q ρ μ := by
  intro r μ' he
  cases he
  exact ⟨_, rfl, h⟩

theorem Holds.unit {Q : Post} {ρ : Env} {μ : Store} (h : Q .unit μ) :
    Holds .unit Q ρ μ := by
  intro r μ' he
  cases he
  exact ⟨_, rfl, h⟩

/-- Reading `x` gives its value `v`, if `x` is bound to `v`. -/
theorem Holds.var {x : String} {v : Value} {Q : Post} {ρ : Env} {μ : Store}
    (hx : ρ.lookup x = some v) (h : Q v μ) : Holds (.var x) Q ρ μ := by
  intro r μ' he
  cases he with
  | var hl =>
    rw [hx] at hl
    cases hl
    exact ⟨_, rfl, h⟩
  | varErr hl =>
    rw [hx] at hl
    cases hl

/-- `a op b`: `a` gives `va`, then `b` gives `vb`, then the operation on `va` and
    `vb` gives a value (no division by zero, no type error) that satisfies `Q`. -/
theorem Holds.binop {op : BinOp} {a b : Expr} {Q : Post} {ρ : Env} {μ : Store}
    (h : Holds a (fun va μ₁ => Holds b (fun vb μ₂ =>
      ∃ v, op.denote va vb = .ok v ∧ Q v μ₂) ρ μ₁) ρ μ) :
    Holds (.binop op a b) Q ρ μ := by
  intro r μ' he
  cases he with
  | binop ha hb =>
    obtain ⟨_, ra, hb'⟩ := h _ _ ha
    cases ra
    obtain ⟨_, rb, v, hv, hq⟩ := hb' _ _ hb
    cases rb
    exact ⟨v, hv, hq⟩
  | binopErrL ha =>
    obtain ⟨_, ra, _⟩ := h _ _ ha
    cases ra
  | binopErrR ha hb =>
    obtain ⟨_, ra, hb'⟩ := h _ _ ha
    cases ra
    obtain ⟨_, rb, _⟩ := hb' _ _ hb
    cases rb

/-- `if c then t else e`: `c` gives a boolean. If it is `true`, `t` satisfies `Q`.
    If it is `false`, `e` satisfies `Q`. -/
theorem Holds.ite {c t e : Expr} {Q : Post} {ρ : Env} {μ : Store}
    (h : Holds c (fun vc μ₁ => vc.isBool = true ∧
      (vc = .bool true → Holds t Q ρ μ₁) ∧ (vc = .bool false → Holds e Q ρ μ₁)) ρ μ) :
    Holds (.ite c t e) Q ρ μ := by
  intro r μ' he
  cases he with
  | ifT hc ht =>
    obtain ⟨_, rc, _, hT, _⟩ := h _ _ hc
    cases rc
    exact hT rfl _ _ ht
  | ifF hc hf =>
    obtain ⟨_, rc, _, _, hF⟩ := h _ _ hc
    cases rc
    exact hF rfl _ _ hf
  | ifNotBool hc hnb =>
    obtain ⟨_, rc, hb, _⟩ := h _ _ hc
    cases rc
    rw [hb] at hnb
    cases hnb
  | ifErr hc =>
    obtain ⟨_, rc, _⟩ := h _ _ hc
    cases rc

/-- `let x = a in b`: `a` gives `v`, then `b`, run with `x` bound to `v`, satisfies
    `Q`. -/
theorem Holds.letin {x : String} {a b : Expr} {Q : Post} {ρ : Env} {μ : Store}
    (h : Holds a (fun v μ₁ => Holds b Q ((x, v) :: ρ) μ₁) ρ μ) :
    Holds (.letin x a b) Q ρ μ := by
  intro r μ' he
  cases he with
  | letin ha hb =>
    obtain ⟨_, ra, hb'⟩ := h _ _ ha
    cases ra
    exact hb' _ _ hb
  | letinErr ha =>
    obtain ⟨_, ra, _⟩ := h _ _ ha
    cases ra

/-- `assert c`: `c` gives `true`, and `Q` holds for `()`. -/
theorem Holds.assert {c : Expr} {Q : Post} {ρ : Env} {μ : Store}
    (h : Holds c (fun vc μ₁ => vc = .bool true ∧ Q .unit μ₁) ρ μ) :
    Holds (.assert c) Q ρ μ := by
  intro r μ' he
  cases he with
  | assert hc =>
    obtain ⟨_, rc, _, hq⟩ := h _ _ hc
    cases rc
    exact ⟨_, rfl, hq⟩
  | assertF hc =>
    obtain ⟨_, rc, hv, _⟩ := h _ _ hc
    cases rc
    cases hv
  | assertNotBool hc hnb =>
    obtain ⟨_, rc, hv, _⟩ := h _ _ hc
    cases rc
    rw [hv] at hnb
    cases hnb
  | assertErr hc =>
    obtain ⟨_, rc, _⟩ := h _ _ hc
    cases rc

end Diva
