import Diva.AbsInt.Domain

/-! # Soundness of the interval operations

Each operation over-approximates its concrete counterpart: for example `mem_add`,
`n ∈ i → m ∈ j → n + m ∈ i.add j`. -/

namespace Diva.AbsInt

/-! ## Bounds -/

namespace Bound

@[simp] theorem fin_le_fin {a b : Int} : fin a ≤ fin b ↔ a ≤ b := by
  simp [LE.le, le]
@[simp] theorem negInf_le (a : Bound) : negInf ≤ a := by simp [LE.le, le]
@[simp] theorem le_posInf (a : Bound) : a ≤ posInf := by cases a <;> simp [LE.le, le]
@[simp] theorem not_posInf_le_fin (n : Int) : ¬ posInf ≤ fin n := by simp [LE.le, le]
@[simp] theorem not_fin_le_negInf (n : Int) : ¬ fin n ≤ negInf := by simp [LE.le, le]
@[simp] theorem not_posInf_le_negInf : ¬ posInf ≤ negInf := by simp [LE.le, le]

theorem le_trans {a b c : Bound} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all; omega

theorem le_total (a b : Bound) : a ≤ b ∨ b ≤ a := by
  cases a <;> cases b <;> simp; omega

theorem min_le {a b n : Bound} (h : a ≤ n) : min a b ≤ n := by
  simp only [min]
  split
  · exact h
  · rename_i hab; exact le_trans ((le_total a b).resolve_left hab) h

theorem min_le' {a b n : Bound} (h : b ≤ n) : min a b ≤ n := by
  simp only [min]
  split
  · rename_i hab; exact le_trans hab h
  · exact h

theorem le_max {a b n : Bound} (h : n ≤ a) : n ≤ max a b := by
  simp only [max]
  split
  · rename_i hab; exact le_trans h hab
  · exact h

theorem le_max' {a b n : Bound} (h : n ≤ b) : n ≤ max a b := by
  simp only [max]
  split
  · exact h
  · rename_i hab; exact le_trans h ((le_total a b).resolve_left hab)

theorem max_le {a b n : Bound} (h1 : a ≤ n) (h2 : b ≤ n) : max a b ≤ n := by
  simp only [max]
  split <;> assumption

theorem le_min {a b n : Bound} (h1 : n ≤ a) (h2 : n ≤ b) : n ≤ min a b := by
  simp only [min]
  split <;> assumption

/-- Adding lower bounds. -/
theorem add_le {a c : Bound} {n m : Int} (h1 : a ≤ fin n) (h2 : c ≤ fin m) :
    a + c ≤ fin (n + m) := by
  show Bound.add a c ≤ _
  cases a <;> cases c <;> simp_all [Bound.add] <;> omega

/-- Adding upper bounds. -/
theorem le_add {b d : Bound} {n m : Int} (h1 : fin n ≤ b) (h2 : fin m ≤ d) :
    fin (n + m) ≤ b + d := by
  show _ ≤ Bound.add b d
  cases b <;> cases d <;> simp_all [Bound.add] <;> omega

theorem neg_le {d : Bound} {m : Int} (h : fin m ≤ d) : -d ≤ fin (-m) := by
  show Bound.neg d ≤ _
  cases d <;> simp_all [Bound.neg] <;> omega

theorem le_neg {a : Bound} {m : Int} (h : a ≤ fin m) : fin (-m) ≤ -a := by
  show _ ≤ Bound.neg a
  cases a <;> simp_all [Bound.neg] <;> omega

end Bound

/-! ## Intervals -/

namespace Itv

open Bound

theorem lin {a b n : Int} (h1 : a ≤ n) (h2 : n ≤ b) (m : Int) :
    min (a * m) (b * m) ≤ n * m ∧ n * m ≤ max (a * m) (b * m) := by
  rcases Int.le_total 0 m with hm | hm
  · have := Int.mul_le_mul_of_nonneg_right h1 hm
    have := Int.mul_le_mul_of_nonneg_right h2 hm; omega
  · have := Int.mul_le_mul_of_nonpos_right h1 hm
    have := Int.mul_le_mul_of_nonpos_right h2 hm; omega

theorem corners {a b c d n m : Int} (h1 : a ≤ n) (h2 : n ≤ b) (h3 : c ≤ m) (h4 : m ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ n * m ∧
    n * m ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have l1 := lin h1 h2 m
  have la := lin h3 h4 a
  have lb := lin h3 h4 b
  rw [Int.mul_comm c a, Int.mul_comm d a, Int.mul_comm m a] at la
  rw [Int.mul_comm c b, Int.mul_comm d b, Int.mul_comm m b] at lb
  omega

theorem mem_singleton (n : Int) : (singleton n).mem n := by simp [mem, singleton]

theorem mem_top (n : Int) : top.mem n := by simp [mem, top]

theorem mem_bot (n : Int) : ¬ bot.mem n := by simp [mem]

theorem mem_leq {i j : Itv} {n : Int} (h : i.mem n) (hl : i.leq j = true) : j.mem n := by
  cases i <;> cases j <;> simp_all [mem, leq]
  exact ⟨le_trans hl.1 h.1, le_trans h.2 hl.2⟩

theorem mem_join_l {i j : Itv} {n : Int} (h : i.mem n) : (i.join j).mem n := by
  cases i <;> cases j <;> simp_all [mem, join]
  exact ⟨min_le h.1, le_max h.2⟩

theorem mem_join_r {i j : Itv} {n : Int} (h : j.mem n) : (i.join j).mem n := by
  cases i <;> cases j <;> simp_all [mem, join]
  exact ⟨min_le' h.1, le_max' h.2⟩

theorem mem_meet {i j : Itv} {n : Int} (h1 : i.mem n) (h2 : j.mem n) : (i.meet j).mem n := by
  cases i <;> cases j <;> simp_all [mem]
  rename_i a b c d
  have lo := max_le h1.1 h2.1
  have hi := le_min h1.2 h2.2
  simp only [meet, ite_eq_left (le_trans lo hi)]
  exact ⟨lo, hi⟩

theorem mem_widen_l {i j : Itv} {n : Int} (h : i.mem n) : (i.widen j).mem n := by
  cases i <;> cases j <;> simp_all [mem, widen]
  constructor
  · split <;> simp_all
  · split <;> simp_all

theorem mem_widen_r {i j : Itv} {n : Int} (h : j.mem n) : (i.widen j).mem n := by
  cases i <;> cases j <;> simp_all [mem, widen]
  constructor
  · split
    · rename_i hac; exact le_trans hac h.1
    · simp
  · split
    · rename_i hdb; exact le_trans h.2 hdb
    · simp

theorem mem_add {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) :
    (i.add j).mem (n + m) := by
  cases i <;> cases j <;> simp_all [mem, add]
  exact ⟨add_le h1.1 h2.1, le_add h1.2 h2.2⟩

theorem mem_sub {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) :
    (i.sub j).mem (n - m) := by
  cases i <;> cases j <;> simp_all [mem, sub]
  rw [Int.sub_eq_add_neg]
  exact ⟨add_le h1.1 (neg_le h2.2), le_add h1.2 (le_neg h2.1)⟩

theorem mem_mul {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) :
    (i.mul j).mem (n * m) := by
  unfold mul
  split
  · simp [mem] at h1
  · simp [mem] at h2
  · simp only [mem, fin_le_fin] at *
    exact corners h1.1 h1.2 h2.1 h2.2
  · rename_i a b c d _
    split
    · rename_i hpos
      simp only [mem, fin_le_fin] at *
      have ha := h1.1
      have hc := h2.1
      have hnm : a * c ≤ n * m := Int.mul_le_mul ha hc hpos.2 (by omega)
      refine ⟨hnm, ?_⟩
      cases b <;> cases d <;> simp_all
    · exact mem_top _
  · exact mem_top _

/-- TODO: truncating division by a constant is monotone (or antitone). -/
theorem mem_div {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) (hm : m ≠ 0) :
    (i.div j).mem (n.tdiv m) := sorry

/-- TODO: `|n mod k| < |k|`, and `0 ≤ n mod k ≤ n` when `0 ≤ n`. -/
theorem mem_mod {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) (hm : m ≠ 0) :
    (i.mod j).mem (n.tmod m) := sorry

theorem cmpLt_sound {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) :
    (n < m → (cmpLt i j).1 = true) ∧ (¬ n < m → (cmpLt i j).2 = true) := by
  cases i with
  | bot => simp [mem] at h1
  | range a b => cases j with
    | bot => simp [mem] at h2
    | range c d =>
      simp only [mem] at h1 h2
      constructor <;> intro h <;> simp only [cmpLt]
      · cases a <;> cases d <;> simp_all; omega
      · cases b <;> cases c <;> simp_all; omega

theorem cmpLe_sound {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) :
    (n ≤ m → (cmpLe i j).1 = true) ∧ (¬ n ≤ m → (cmpLe i j).2 = true) := by
  cases i with
  | bot => simp [mem] at h1
  | range a b => cases j with
    | bot => simp [mem] at h2
    | range c d =>
      simp only [mem] at h1 h2
      constructor <;> intro h <;> simp only [cmpLe]
      · cases a <;> cases d <;> simp_all; omega
      · cases b <;> cases c <;> simp_all; omega

theorem cmpEq_sound {i j : Itv} {n m : Int} (h1 : i.mem n) (h2 : j.mem m) :
    (n = m → (cmpEq i j).1 = true) ∧ (¬ n = m → (cmpEq i j).2 = true) := by
  cases i with
  | bot => simp [mem] at h1
  | range a b => cases j with
    | bot => simp [mem] at h2
    | range c d =>
      simp only [mem] at h1 h2
      constructor <;> intro h <;> simp only [cmpEq]
      · cases b <;> cases c <;> cases d <;> cases a <;> simp_all <;> omega
      · cases a <;> cases b <;> cases c <;> cases d <;> simp_all <;> omega

end Itv

end Diva.AbsInt
