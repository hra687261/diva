import Diva.Semantics

/-!
# Integer intervals

An interval `[lo, hi]` over-approximates a set of integers. Its bounds are
integers or `±∞` (`Bound`), and `bot` is the empty interval. Every operation is
executable, so the kernel can run the analysis itself (`decide`). The soundness
lemmas are in `Diva.AbsInt.SoundItv`.
-/

namespace Diva.AbsInt

/-! ## Bounds: integers extended with `±∞` -/

inductive Bound where
  | negInf
  | fin (n : Int)
  | posInf
  deriving DecidableEq, Repr, Inhabited

namespace Bound

def le : Bound → Bound → Bool
  | negInf, _ => true
  | _, posInf => true
  | fin a, fin b => decide (a ≤ b)
  | _, _ => false

instance : LE Bound := ⟨fun a b => a.le b = true⟩
instance (a b : Bound) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.le b = true))
instance : Min Bound := ⟨fun a b => if a ≤ b then a else b⟩
instance : Max Bound := ⟨fun a b => if a ≤ b then b else a⟩

/-- `+-∞` absorbs (lower bounds are added to lower bounds, upper bounds are
    added to upper bounds) so `-∞ + +∞` never arises for a non-empty interval.
-/
def add : Bound → Bound → Bound
  | negInf, _ | _, negInf => negInf
  | posInf, _ | _, posInf => posInf
  | fin a, fin b => fin (a + b)

def neg : Bound → Bound
  | negInf => posInf
  | fin a => fin (-a)
  | posInf => negInf

instance : Add Bound := ⟨add⟩
instance : Neg Bound := ⟨neg⟩
instance : Sub Bound := ⟨fun a b => a + -b⟩

/-- Truncating division by a non-zero constant `k`. -/
def divBy (k : Int) : Bound → Bound
  | fin n => fin (n.tdiv k)
  | negInf => if 0 < k then negInf else posInf
  | posInf => if 0 < k then posInf else negInf

instance : ToString Bound where
  toString
    | negInf => "-∞"
    | fin n => toString n
    | posInf => "+∞"

end Bound

/-! ## Intervals -/

inductive Itv where
  | bot                     -- the empty interval
  | range (lo hi : Bound)   -- `[lo, hi]`
  deriving DecidableEq, Repr, Inhabited

namespace Itv

open Bound

def mem : Itv → Int → Prop
  | bot, _ => False
  | range lo hi, n => lo ≤ fin n ∧ fin n ≤ hi

def top : Itv := range negInf posInf
def singleton (n : Int) : Itv := range (fin n) (fin n)

/-- The only integer in the interval, if there is exactly one. -/
def asConst : Itv → Option Int
  | range (fin a) (fin b) => if a = b then some a else none
  | _ => none

/-- Inclusion. -/
def leq : Itv → Itv → Bool
  | bot, _ => true
  | _, bot => false
  | range a b, range c d => decide (c ≤ a) && decide (b ≤ d)

def join : Itv → Itv → Itv
  | bot, i | i, bot => i
  | range a b, range c d => range (min a c) (max b d)

def meet : Itv → Itv → Itv
  | range a b, range c d => if max a c ≤ min b d then range (max a c) (min b d) else bot
  | _, _ => bot

/-- Standard widening: jump to `±∞` when the new interval is wider than the
    original. -/
def widen : Itv → Itv → Itv
  | bot, i | i, bot => i
  | range a b, range c d => range (if a ≤ c then a else negInf) (if d ≤ b then b else posInf)

def add : Itv → Itv → Itv
  | range a b, range c d => range (a + c) (b + d)
  | _, _ => bot

def sub : Itv → Itv → Itv
  | range a b, range c d => range (a - d) (b - c)
  | _, _ => bot

/-- Multiplication: incomplete. -/
def mul : Itv → Itv → Itv
  | bot, _ | _, bot => bot
  | range (fin a) (fin b), range (fin c) (fin d) =>
    range (fin (min (min (a * c) (a * d)) (min (b * c) (b * d))))
       (fin (max (max (a * c) (a * d)) (max (b * c) (b * d))))
  | range (fin a) _, range (fin c) _ =>
    if 0 ≤ a ∧ 0 ≤ c then
      range (fin (a * c)) posInf  -- not all bounds are finite (previous case)
    else top
  | _, _ => top

/-- Truncating division by a non-zero constant, otherwise unknown. -/
def div : Itv → Itv → Itv
  | bot, _ | _, bot => bot
  | range a b, range (fin k) (fin k') =>
    if k = k' ∧ 0 < k then range (a.divBy k) (b.divBy k)
    else if k = k' ∧ k < 0 then range (b.divBy k) (a.divBy k)
    else top
  | _, _ => top

/-- `[a, b] mod k` for a non-zero constant `k` (the result has the sign of the
    dividend, like OCaml): within `±(|k| - 1)`, and in `[0, min (|k| - 1) b]`
    when `a ≥ 0`. -/
def mod : Itv → Itv → Itv
  | bot, _ | _, bot => bot
  | range a b, range (fin k) (fin k') =>
    if k = k' ∧ k ≠ 0 then
      let m : Int := k.natAbs - 1
      if fin 0 ≤ a then range (fin 0) (min (fin m) b) else range (fin (-m)) (fin m)
    else top
  | _, _ => top

/-- Narrow `x ∈ i`, `y ∈ j` assuming `x < y`: `x ≤ hi j - 1` and `y ≥ lo i + 1`. -/
def assumeLt : Itv → Itv → Itv × Itv
  | range a b, range c d =>
    ((range a b).meet (range negInf (d + fin (-1))), (range c d).meet (range (a + fin 1) posInf))
  | _, _ => (bot, bot)

/-- Narrow `x ∈ i`, `y ∈ j` assuming `x ≤ y`: `x ≤ hi j` and `y ≥ lo i`. -/
def assumeLe : Itv → Itv → Itv × Itv
  | range a b, range c d =>
    ((range a b).meet (range negInf d), (range c d).meet (range a posInf))
  | _, _ => (bot, bot)

/-- `(may be true, may be false)` for `x < y`, `x ∈ i`, `y ∈ j`. -/
def cmpLt : Itv → Itv → Bool × Bool
  | range a b, range c d =>
    let surely := match b, c with | fin x, fin y => decide (x < y) | _, _ => false
    let never := match a, d with | fin x, fin y => decide (y ≤ x) | _, _ => false
    (!never, !surely)
  | _, _ => (false, false)

/-- `(may be true, may be false)` for `x ≤ y`. -/
def cmpLe : Itv → Itv → Bool × Bool
  | range a b, range c d =>
    let surely := match b, c with | fin x, fin y => decide (x ≤ y) | _, _ => false
    let never := match a, d with | fin x, fin y => decide (y < x) | _, _ => false
    (!never, !surely)
  | _, _ => (false, false)

/-- `(may be true, may be false)` for `x = y`. -/
def cmpEq : Itv → Itv → Bool × Bool
  | range a b, range c d =>
    let surely := match a, b, c, d with
      | fin w, fin x, fin y, fin z => decide (w = x) && decide (x = y) && decide (y = z)
      | _, _, _, _ => false
    let never :=
      (match b, c with | fin x, fin y => decide (x < y) | _, _ => false) ||
      (match d, a with | fin x, fin y => decide (x < y) | _, _ => false)
    (!never, !surely)
  | _, _ => (false, false)

instance : ToString Itv where
  toString
    | bot => "⊥"
    | range (fin a) (fin b) => if a == b then s!"{a}" else s!"[{a}, {b}]"
    | range a b => s!"[{a}, {b}]"

end Itv

end Diva.AbsInt
