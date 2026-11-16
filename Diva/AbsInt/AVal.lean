import Diva.AbsInt.Framework
import Diva.Semantics

/-!
# Abstract values

A `Flat A` describes a set of values of any kind: the integers by the numeric domain
`A`, booleans by value (`tt`, `ff`), and every other kind by a flag saying whether
the value may be of that kind.

An `AVal A` adds a *summary* `(P, R)` for the closures it may be: called with an
argument in `P`, they return a value in `R` (if they return). Summaries are over
`Flat`, so a closure returned by a closure loses its summary.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

/-- A product (one component per kind) rather than one constructor per kind, because
    a value may be of several kinds (the core language is untyped), and even
    well-typed OCaml mixes them once compiled to Lambda (`None` is `0`, `Some x` a
    block). -/
structure Flat (A : Type) where
  int  : A      -- the integers it may be (`bot`: none)
  tt   : Bool   -- may be `true`
  ff   : Bool   -- may be `false`
  unit : Bool   -- may be `()`
  list : Bool   -- may be a list
  fn   : Bool   -- may be a closure
  loc  : Bool   -- may be an array or a ref
  exn  : Bool   -- may be an exception
  deriving Inhabited

namespace Flat

variable {A : Type} [NumDomain A]

/-- No value at all. -/
def bot : Flat A := ⟨AbsDomain.bot, false, false, false, false, false, false, false⟩

/-- Any value. -/
def top : Flat A := ⟨AbsDomain.top, true, true, true, true, true, true, true⟩

def ofInt (i : A) : Flat A := { (bot : Flat A) with int := i }
/-- A boolean that may be `true` (`t`) or `false` (`f`). -/
def bools (t f : Bool) : Flat A := { (bot : Flat A) with tt := t, ff := f }
def unitV : Flat A := { (bot : Flat A) with unit := true }
def listV : Flat A := { (bot : Flat A) with list := true }
def fnV : Flat A := { (bot : Flat A) with fn := true }
def exnV : Flat A := { (bot : Flat A) with exn := true }

def join (a b : Flat A) : Flat A :=
  ⟨AbsDomain.join a.int b.int, a.tt || b.tt, a.ff || b.ff, a.unit || b.unit,
   a.list || b.list, a.fn || b.fn, a.loc || b.loc, a.exn || b.exn⟩

def leq (a b : Flat A) : Bool :=
  AbsDomain.leq a.int b.int && (!a.tt || b.tt) && (!a.ff || b.ff) && (!a.unit || b.unit) &&
  (!a.list || b.list) && (!a.fn || b.fn) && (!a.loc || b.loc) && (!a.exn || b.exn)

/-- Concretisation: the values `a` describes. -/
def mem (a : Flat A) : Value → Prop
  | .int n => γ a.int n
  | .bool true => a.tt = true
  | .bool false => a.ff = true
  | .unit => a.unit = true
  | .nil | .cons _ _ => a.list = true
  | .clos .. => a.fn = true
  | .arr _ | .ref _ => a.loc = true
  | .exn _ _ => a.exn = true

theorem mem_top (v : Value) : (top : Flat A).mem v := by
  cases v
  case int n => exact top_sound n
  case bool b => cases b <;> rfl
  all_goals rfl

theorem mem_join_l {a b : Flat A} {v : Value} (h : a.mem v) : (a.join b).mem v := by
  cases v
  case int n => exact join_sound_l h
  case bool c => cases c <;> simp_all [mem, join]
  all_goals simp_all [mem, join]

theorem mem_join_r {a b : Flat A} {v : Value} (h : b.mem v) : (a.join b).mem v := by
  cases v
  case int n => exact join_sound_r h
  case bool c => cases c <;> simp_all [mem, join]
  all_goals simp_all [mem, join]

theorem mem_leq {a b : Flat A} {v : Value} (h : a.mem v) (hl : a.leq b = true) : b.mem v := by
  simp only [leq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hl
  cases v
  case int n => exact leq_sound h hl.1.1.1.1.1.1.1
  case bool c => cases c <;> simp_all [mem]
  all_goals simp_all [mem]

/-- A comparison's result: `true` if it may hold, `false` if it may not. -/
theorem mem_bools {p : Bool × Bool} {P : Prop} [Decidable P]
    (h : (P → p.1 = true) ∧ (¬ P → p.2 = true)) :
    (bools p.1 p.2 : Flat A).mem (.bool (decide P)) := by
  by_cases hP : P
  · simp [mem, bools, hP, h.1 hP]
  · simp [mem, bools, hP, h.2 hP]

instance [ToString A] : ToString (Flat A) where
  toString a :=
    if top.leq a then "⊤" else
    let parts :=
      (if AbsDomain.leq a.int AbsDomain.bot then [] else [toString a.int]) ++
      (match a.tt, a.ff with
        | true, true => ["bool"] | true, false => ["true"]
        | false, true => ["false"] | false, false => []) ++
      (if a.unit then ["()"] else []) ++ (if a.list then ["list"] else []) ++
      (if a.fn then ["fun"] else []) ++ (if a.loc then ["loc"] else []) ++
      (if a.exn then ["exn"] else [])
    if parts.isEmpty then "⊥" else " | ".intercalate parts

end Flat

/-! ## Function summaries -/

/-- `(P, R)`: called with an argument in `P`, a closure returns a value in `R` (if it
    returns). -/
abbrev Summary (A : Type) := Flat A × Flat A

/-- The closure `clos s x b ρ` satisfies the summary `S`. -/
def Sat [NumDomain A] (S : Summary A) (s : Option String) (x : String) (b : Expr)
    (ρ : Env) : Prop :=
  ∀ v w μ μ', S.1.mem v → Eval (callEnv s x b ρ v) μ b (.ok w) μ' → S.2.mem w

/-- `Flat`, plus a summary that the closures it may be satisfy (`fn`: any closure). -/
structure AVal (A : Type) extends Flat A where
  sum : Option (Summary A)
  deriving Inhabited

namespace AVal

variable {A : Type} [NumDomain A]

def ofFlat (f : Flat A) : AVal A := { toFlat := f, sum := none }

def bot : AVal A := ofFlat Flat.bot
def top : AVal A := ofFlat Flat.top
def ofInt (i : A) : AVal A := ofFlat (Flat.ofInt i)
def bools (t f : Bool) : AVal A := ofFlat (Flat.bools t f)
def unitV : AVal A := ofFlat Flat.unitV
def listV : AVal A := ofFlat Flat.listV
/-- Any closure. -/
def fnV : AVal A := ofFlat Flat.fnV
def exnV : AVal A := ofFlat Flat.exnV
/-- The closures that satisfy `S`. -/
def summary (S : Summary A) : AVal A := { toFlat := Flat.bot, sum := some S }

/-- Forget the summary: its closures become "any closure". -/
def flat (a : AVal A) : Flat A := { a.toFlat with fn := a.fn || a.sum.isSome }

/-- Summaries are kept when they have the same precondition, forgotten otherwise. -/
def join (a b : AVal A) : AVal A :=
  match a.sum, b.sum with
  | some S, some T =>
    if S.1.leq T.1 && T.1.leq S.1 then
      { toFlat := a.toFlat.join b.toFlat, sum := some (S.1, S.2.join T.2) }
    else ofFlat (a.flat.join b.flat)
  | some S, none => { toFlat := a.toFlat.join b.toFlat, sum := some S }
  | none, s => { toFlat := a.toFlat.join b.toFlat, sum := s }

/-- The closures described by the summary. -/
def sumMem (a : AVal A) : Value → Prop
  | .clos s x b ρ => ∃ S, a.sum = some S ∧ Sat S s x b ρ
  | _ => False

/-- Concretisation: the values `a` describes. -/
def mem (a : AVal A) (v : Value) : Prop := a.toFlat.mem v ∨ a.sumMem v

theorem mem_ofFlat {f : Flat A} {v : Value} (h : f.mem v) : (ofFlat f).mem v := .inl h

theorem mem_top (v : Value) : (top : AVal A).mem v := .inl (Flat.mem_top v)

theorem mem_bools {p : Bool × Bool} {P : Prop} [Decidable P]
    (h : (P → p.1 = true) ∧ (¬ P → p.2 = true)) :
    (bools p.1 p.2 : AVal A).mem (.bool (decide P)) := .inl (Flat.mem_bools h)

theorem mem_int {a : AVal A} {n : Int} (h : a.mem (.int n)) : γ a.int n := by
  rcases h with h | h
  · exact h
  · simp [sumMem] at h

theorem mem_tt {a : AVal A} (h : a.mem (.bool true)) : a.tt = true := by
  rcases h with h | h
  · exact h
  · simp [sumMem] at h

theorem mem_ff {a : AVal A} (h : a.mem (.bool false)) : a.ff = true := by
  rcases h with h | h
  · exact h
  · simp [sumMem] at h

/-- Two values with the same summary describe the same closures. -/
theorem sumMem_of_eq {a b : AVal A} {v : Value} (hs : a.sum = b.sum) (h : a.sumMem v) :
    b.sumMem v := by
  cases v <;> simp_all [sumMem]

theorem mem_flat {a : AVal A} {v : Value} (h : a.mem v) : a.flat.mem v := by
  rcases h with h | h
  · -- the same values, and possibly more closures
    cases v
    case bool c => cases c <;> simp_all [Flat.mem, flat]
    all_goals simp_all [Flat.mem, flat]
  · -- a closure of the summary: now "any closure"
    cases v <;> simp only [sumMem] at h
    obtain ⟨S, hS, -⟩ := h
    simp [Flat.mem, flat, hS]

theorem mem_join_l {a b : AVal A} {v : Value} (h : a.mem v) : (a.join b).mem v := by
  unfold join
  split
  next S T hS hT =>
    split
    next hpre =>
      rcases h with h | h
      · exact .inl (Flat.mem_join_l h)
      · -- the closure satisfies `S`, so also `(S.1, S.2 ⊔ T.2)`
        cases v <;> simp only [sumMem] at h
        obtain ⟨S', hS', hsat⟩ := h
        rw [hS] at hS'; cases hS'
        exact .inr ⟨_, rfl, fun v w μ μ' hv hev => Flat.mem_join_l (hsat v w μ μ' hv hev)⟩
    next => exact .inl (Flat.mem_join_l (mem_flat h))
  next S hS hT =>
    rcases h with h | h
    · exact .inl (Flat.mem_join_l h)
    · exact .inr (sumMem_of_eq (by simp [hS]) h)
  next s hS hT =>
    rcases h with h | h
    · exact .inl (Flat.mem_join_l h)
    · cases v <;> simp_all [sumMem]

theorem mem_join_r {a b : AVal A} {v : Value} (h : b.mem v) : (a.join b).mem v := by
  unfold join
  split
  next S T hS hT =>
    split
    next hpre =>
      simp only [Bool.and_eq_true] at hpre
      rcases h with h | h
      · exact .inl (Flat.mem_join_r h)
      · -- the closure satisfies `T`, and `S.1 ⊆ T.1`, so also `(S.1, S.2 ⊔ T.2)`
        cases v <;> simp only [sumMem] at h
        obtain ⟨T', hT', hsat⟩ := h
        rw [hT] at hT'; cases hT'
        refine .inr ⟨_, rfl, fun v w μ μ' hv hev => ?_⟩
        exact Flat.mem_join_r (hsat v w μ μ' (Flat.mem_leq hv hpre.1) hev)
    next => exact .inl (Flat.mem_join_r (mem_flat h))
  next S hS hT =>
    rcases h with h | h
    · exact .inl (Flat.mem_join_r h)
    · cases v <;> simp_all [sumMem]
  next s hS hT =>
    rcases h with h | h
    · exact .inl (Flat.mem_join_r h)
    · exact .inr (sumMem_of_eq (by simp) h)

instance [ToString A] : ToString (AVal A) where
  toString a :=
    match a.sum with
    | none => toString a.toFlat
    | some (P, R) =>
      let f := s!"fun {P} -> {R}"
      if toString a.toFlat == "⊥" then f else s!"{a.toFlat} | {f}"

end AVal

end Diva.AbsInt
