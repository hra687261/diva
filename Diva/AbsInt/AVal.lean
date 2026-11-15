import Diva.AbsInt.Framework
import Diva.Semantics

/-!
# Abstract values

An `AVal A` describes a set of values of any kind (the integers are described by
the numeric domain `A`). For every other kind, a flag says whether the value may
be of that kind. Booleans are tracked by value (`tt`, `ff`), and lists,
closures, arrays, refs, and exceptions only by kind, for now.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

/-- A product (one component per kind) rather than one constructor per kind, because
    a value may be of several kinds (the core language is untyped), and even
    well-typed OCaml mixes them once compiled to Lambda (`None` is `0`, `Some x` a
    block). -/
structure AVal (A : Type) where
  int  : A      -- the integers it may be (`bot`: none)
  tt   : Bool   -- may be `true`
  ff   : Bool   -- may be `false`
  unit : Bool   -- may be `()`
  list : Bool   -- may be a list
  fn   : Bool   -- may be a closure
  loc  : Bool   -- may be an array or a ref
  exn  : Bool   -- may be an exception
  deriving Inhabited

namespace AVal

variable {A : Type} [NumDomain A]

/-- No value at all. -/
def bot : AVal A := ⟨AbsDomain.bot, false, false, false, false, false, false, false⟩

/-- Any value. -/
def top : AVal A := ⟨AbsDomain.top, true, true, true, true, true, true, true⟩

def ofInt (i : A) : AVal A := { (bot : AVal A) with int := i }
/-- A boolean that may be `true` (`t`) or `false` (`f`). -/
def bools (t f : Bool) : AVal A := { (bot : AVal A) with tt := t, ff := f }
def unitV : AVal A := { (bot : AVal A) with unit := true }
def listV : AVal A := { (bot : AVal A) with list := true }
def fnV : AVal A := { (bot : AVal A) with fn := true }
def exnV : AVal A := { (bot : AVal A) with exn := true }

def join (a b : AVal A) : AVal A :=
  ⟨AbsDomain.join a.int b.int, a.tt || b.tt, a.ff || b.ff, a.unit || b.unit,
   a.list || b.list, a.fn || b.fn, a.loc || b.loc, a.exn || b.exn⟩

def leq (a b : AVal A) : Bool :=
  AbsDomain.leq a.int b.int && (!a.tt || b.tt) && (!a.ff || b.ff) && (!a.unit || b.unit) &&
  (!a.list || b.list) && (!a.fn || b.fn) && (!a.loc || b.loc) && (!a.exn || b.exn)

/-- Concretisation: the values `a` describes. -/
def mem (a : AVal A) : Value → Prop
  | .int n => γ a.int n
  | .bool true => a.tt = true
  | .bool false => a.ff = true
  | .unit => a.unit = true
  | .nil | .cons _ _ => a.list = true
  | .clos .. => a.fn = true
  | .arr _ | .ref _ => a.loc = true
  | .exn _ _ => a.exn = true

theorem mem_top (v : Value) : (top : AVal A).mem v := by
  cases v
  case int n => exact top_sound n
  case bool b => cases b <;> rfl
  all_goals rfl

theorem mem_join_l {a b : AVal A} {v : Value} (h : a.mem v) : (a.join b).mem v := by
  cases v
  case int n => exact join_sound_l h
  case bool c => cases c <;> simp_all [mem, join]
  all_goals simp_all [mem, join]

theorem mem_join_r {a b : AVal A} {v : Value} (h : b.mem v) : (a.join b).mem v := by
  cases v
  case int n => exact join_sound_r h
  case bool c => cases c <;> simp_all [mem, join]
  all_goals simp_all [mem, join]

theorem mem_leq {a b : AVal A} {v : Value} (h : a.mem v) (hl : a.leq b = true) : b.mem v := by
  simp only [leq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hl
  cases v
  case int n => exact leq_sound h hl.1.1.1.1.1.1.1
  case bool c => cases c <;> simp_all [mem]
  all_goals simp_all [mem]

/-- A comparison's result: `true` if it may hold, `false` if it may not. -/
theorem mem_bools {p : Bool × Bool} {P : Prop} [Decidable P]
    (h : (P → p.1 = true) ∧ (¬ P → p.2 = true)) :
    (bools p.1 p.2 : AVal A).mem (.bool (decide P)) := by
  by_cases hP : P
  · simp [mem, bools, hP, h.1 hP]
  · simp [mem, bools, hP, h.2 hP]

instance [ToString A] : ToString (AVal A) where
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

end AVal

end Diva.AbsInt
