import Diva.AbsInt.Framework
import Diva.Semantics

/-!
# Abstract values

A `Flat A` describes a set of values of any kind: the integers by the numeric domain
`A`, booleans by value (`tt`, `ff`), and every other kind by a flag saying whether
the value may be of that kind.

An `AVal A` adds a *summary* for the closures it may be: called with an argument in
`pre`, they return a value in `res` (if they return), and fail only if `fails` is `true`.
Summaries are over `Flat`, so a closure returned by a closure loses its summary.
Which values an `AVal` describes is defined with `aeval` (`AVal.mem`, in
`Aeval.lean`).
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

/-- `a` describes no more values than `b`. -/
def sub (a b : Flat A) : Prop := ∀ v, a.mem v → b.mem v

theorem sub_refl (a : Flat A) : a.sub a := fun _ h => h

/-- Each element of `as` does not describe more values than the one at the same
    place in `bs`, and the lists have the same length. -/
def subs : List (Flat A) → List (Flat A) → Prop
  | [], [] => True
  | a :: as, b :: bs => a.sub b ∧ subs as bs
  | _, _ => False

theorem subs_refl : (as : List (Flat A)) → subs as as
  | [] => trivial
  | a :: as => ⟨sub_refl a, subs_refl as⟩

/-- `leq` on each element, and the lists have the same length. -/
def leqs : List (Flat A) → List (Flat A) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.leq b && leqs as bs
  | _, _ => false

/-- `as ≤ bs` and `bs ⊆ cs` give `as ⊆ cs`. -/
theorem subs_of_leqs : (as bs cs : List (Flat A)) → leqs as bs = true → subs bs cs →
    subs as cs
  | [], [], [], _, _ => trivial
  | a :: as, b :: bs, c :: cs, hl, hs => by
    simp only [leqs, Bool.and_eq_true] at hl
    exact ⟨fun v hv => hs.1 v (mem_leq hv hl.1), subs_of_leqs as bs cs hl.2 hs.2⟩
  | [], _ :: _, _, hl, _ | _ :: _, [], _, hl, _ => by simp [leqs] at hl
  | [], [], _ :: _, _, hs | _ :: _, _ :: _, [], _, hs => by simp [subs] at hs

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

/-- What calling a closure gives. Called with an argument in `pre`, it returns:
    - if `rest` is empty, a value in `res`, and an error only if `fails` is `true`;
    - otherwise a closure (it is curried), whose summary is
      `⟨rest.head, rest.tail, res, fails⟩`. -/
structure Summary (A : Type) where
  pre : Flat A
  rest : List (Flat A)
  res : Flat A
  fails : Bool
  deriving Inhabited

/-- The closure `clos s x b ρ` satisfies the summary `S`, when `S.rest` is empty. -/
def Sat [NumDomain A] (S : Summary A) (s : Option String) (x : String) (b : Expr)
    (ρ : Env) : Prop :=
  ∀ v w μ μ', S.pre.mem v → Eval (callEnv s x b ρ v) μ b (.ok w) μ' → S.res.mem w

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

/-- Summaries are kept when they have the same preconditions, forgotten otherwise. -/
def join (a b : AVal A) : AVal A :=
  match a.sum, b.sum with
  | some S, some T =>
    if S.pre.leq T.pre && T.pre.leq S.pre && Flat.leqs S.rest T.rest &&
        Flat.leqs T.rest S.rest then
      { toFlat := a.toFlat.join b.toFlat,
        sum := some ⟨S.pre, S.rest, S.res.join T.res, S.fails || T.fails⟩ }
    else ofFlat (a.flat.join b.flat)
  | some S, none => { toFlat := a.toFlat.join b.toFlat, sum := some S }
  | none, s => { toFlat := a.toFlat.join b.toFlat, sum := s }

instance [ToString A] : ToString (AVal A) where
  toString a :=
    match a.sum with
    | none => toString a.toFlat
    | some S =>
      let f := s!"fun {" -> ".intercalate ((S.pre :: S.rest).map toString)} -> {S.res}"
      if toString a.toFlat == "⊥" then f else s!"{a.toFlat} | {f}"

end AVal

end Diva.AbsInt
