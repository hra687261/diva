/-!
# Abstract domains, with their soundness obligations

A domain gives its operations *and* a concretisation `γ` (which concrete values
an abstract value describes), with one soundness obligation per operation. An
instance can't be declared without proving them (or writing a visible `sorry`).

Soundness needs no lattice laws, only that each operation over-approximates its
concrete counterpart.
-/

namespace Diva.AbsInt

/-- An abstract domain `A` describing concrete values of type `C`. -/
class AbsDomain (A : Type) (C : outParam Type) where
  γ : A → C → Prop
  top : A
  bot : A
  leq : A → A → Bool
  join : A → A → A
  meet : A → A → A
  widen : A → A → A
  top_sound : ∀ c, γ top c
  bot_sound : ∀ c, ¬ γ bot c
  leq_sound : ∀ {a b c}, γ a c → leq a b = true → γ b c
  join_sound_l : ∀ {a b c}, γ a c → γ (join a b) c
  join_sound_r : ∀ {a b c}, γ b c → γ (join a b) c
  meet_sound : ∀ {a b c}, γ a c → γ b c → γ (meet a b) c
  widen_sound_l : ∀ {a b c}, γ a c → γ (widen a b) c
  widen_sound_r : ∀ {a b c}, γ b c → γ (widen a b) c

/-- A domain for integers, with the arithmetic of `BinOp.denote`. -/
class NumDomain (A : Type) extends AbsDomain A Int where
  const : Int → A
  /-- The only integer `a` describes, if `a` is a singleton, `none` otherwise. -/
  asConst : A → Option Int
  add : A → A → A
  sub : A → A → A
  mul : A → A → A
  div : A → A → A
  mod : A → A → A
  /-- Comparisons, as `(may be true, may be false)`. -/
  cmpLt : A → A → Bool × Bool
  cmpLe : A → A → Bool × Bool
  cmpEq : A → A → Bool × Bool
  /-- Narrow both sides assuming `x < y` (resp. `x ≤ y`). -/
  assumeLt : A → A → A × A
  assumeLe : A → A → A × A
  const_sound : ∀ n, γ (const n) n
  asConst_sound : ∀ {a n m}, asConst a = some n → γ a m → m = n
  add_sound : ∀ {a b n m}, γ a n → γ b m → γ (add a b) (n + m)
  sub_sound : ∀ {a b n m}, γ a n → γ b m → γ (sub a b) (n - m)
  mul_sound : ∀ {a b n m}, γ a n → γ b m → γ (mul a b) (n * m)
  div_sound : ∀ {a b n m}, γ a n → γ b m → m ≠ 0 → γ (div a b) (n.tdiv m)
  mod_sound : ∀ {a b n m}, γ a n → γ b m → m ≠ 0 → γ (mod a b) (n.tmod m)
  cmpLt_sound : ∀ {a b n m}, γ a n → γ b m →
    (n < m → (cmpLt a b).1 = true) ∧ (¬ n < m → (cmpLt a b).2 = true)
  cmpLe_sound : ∀ {a b n m}, γ a n → γ b m →
    (n ≤ m → (cmpLe a b).1 = true) ∧ (¬ n ≤ m → (cmpLe a b).2 = true)
  cmpEq_sound : ∀ {a b n m}, γ a n → γ b m →
    (n = m → (cmpEq a b).1 = true) ∧ (¬ n = m → (cmpEq a b).2 = true)
  assumeLt_sound : ∀ {a b n m}, γ a n → γ b m → n < m →
    γ (assumeLt a b).1 n ∧ γ (assumeLt a b).2 m
  assumeLe_sound : ∀ {a b n m}, γ a n → γ b m → n ≤ m →
    γ (assumeLe a b).1 n ∧ γ (assumeLe a b).2 m

end Diva.AbsInt
