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
    a value may be of several kinds: the core language is untyped.

    The last three fields describe the parts of lists and of ADT values (values of
    algebraic data types: `C v`, the constructor `C` applied to `v`), each by a
    `Flat`. `mem` ignores them: for `mem`, a `Flat` with `list` describes every list,
    whatever its elements, and with `ctor` every ADT value, whatever its argument. So
    only the analysis that isn't proved yet uses them (see `aevalM`). -/
structure Flat (A : Type) where
  int  : A      -- the integers it may be (`bot`: none)
  tt   : Bool   -- may be `true`
  ff   : Bool   -- may be `false`
  unit : Bool   -- may be `()`
  list : Bool   -- may be a list
  fn   : Bool   -- may be a closure
  loc  : Bool   -- may be an array or a ref
  ctor : Bool   -- may be a constructor applied to an argument (an exception, ...)
  /-- The allocation sites of the refs it may be, for the analysis of the store (see
      `aevalM`). `mem` ignores them: for `mem`, a `Flat` with `loc` describes every
      array and ref, whatever its site. So only the analysis that isn't proved yet uses
      them. -/
  refs : List Nat := []
  /-- The allocation sites of the arrays it may be, as `refs`. -/
  arrs : List Nat := []
  /-- The constructors `C` of the values `C v` it may be, for the analysis of exceptions
      and constructors (see `aevalM`). `mem` ignores them: for `mem`, a `Flat` with
      `ctor` describes every value `C v`, whatever its constructor. So only the analysis
      that isn't proved yet uses them. -/
  ctors : List String := []
  /-- The elements of the lists it may be, if `list`. `none`: any elements. -/
  elem : Option (Flat A) := none
  /-- The lists it may be, element by element, if they all have this length: a tuple's
      components, for example. If `items` is `some ws`, `elem` contains each of `ws`. -/
  items : Option (List (Flat A)) := none
  /-- The arguments `v` of the values `C v`, for the constructors `C` of `ctors`. A
      constructor without an entry may have any argument. -/
  args : List (String × Flat A) := []
  /-- If `list`: the lists it describes may be `[]`. -/
  empty : Bool := true
  deriving Inhabited

namespace Flat

variable {A : Type} [NumDomain A]

/-- No value at all. -/
def bot : Flat A :=
  ⟨AbsDomain.bot, false, false, false, false, false, false, false, [], [], [], none, none, [],
   false⟩

/-- Any value. -/
def top : Flat A :=
  ⟨AbsDomain.top, true, true, true, true, true, true, true, [], [], [], none, none, [], true⟩

def ofInt (i : A) : Flat A := { (bot : Flat A) with int := i }
/-- A boolean that may be `true` (`t`) or `false` (`f`). -/
def bools (t f : Bool) : Flat A := { (bot : Flat A) with tt := t, ff := f }
def unitV : Flat A := { (bot : Flat A) with unit := true }
def listV : Flat A := { (bot : Flat A) with list := true, empty := true }
def fnV : Flat A := { (bot : Flat A) with fn := true }
def ctorV : Flat A := { (bot : Flat A) with ctor := true }

/-- `join` without the parts of lists and of ADT values. -/
def joinBase (a b : Flat A) : Flat A :=
  ⟨AbsDomain.join a.int b.int, a.tt || b.tt, a.ff || b.ff, a.unit || b.unit,
   a.list || b.list, a.fn || b.fn, a.loc || b.loc, a.ctor || b.ctor,
   (a.refs ++ b.refs).eraseDups, (a.arrs ++ b.arrs).eraseDups, (a.ctors ++ b.ctors).eraseDups,
   none, none, [], (a.list && a.empty) || (b.list && b.empty)⟩

/-
The functions on the parts are recursive. Lean accepts their recursion only if they take
`Flat` apart by its constructor, not with projections such as `a.elem`. The lemmas
`join_eq` and `leq_eq` give them with projections, for the proofs.
-/

mutual

/-- The values that `a` or `b` describe. -/
def join : Flat A → Flat A → Flat A
  | a@⟨_, _, _, _, la, _, _, xa, _, _, ta, ea, ia, aa, _⟩,
    b@⟨_, _, _, _, lb, _, _, xb, _, _, tb, eb, ib, ab, _⟩ =>
    { joinBase a b with
      elem := joinElem la lb ea eb, items := joinItems la lb ia ib,
      args := joinArgs xa xb ta tb aa ab }
termination_by structural a _ => a

/-- The elements of the lists of `a` or `b`, from whether they may be lists (`la`, `lb`)
    and their elements (`ea`, `eb`). -/
def joinElem : Bool → Bool → Option (Flat A) → Option (Flat A) → Option (Flat A)
  | true, true, some x, some y => some (join x y)
  | true, false, x, _ => x
  | false, true, _, y => y
  | _, _, _, _ => none
termination_by structural _ _ ea _ => ea

/-- The lists of `a` or `b` element by element: kept if both give them with the same
    length, or if only one of them may be a list. -/
def joinItems : Bool → Bool → Option (List (Flat A)) → Option (List (Flat A)) →
    Option (List (Flat A))
  | _, _, some xs, some ys => if xs.length == ys.length then some (joinList xs ys) else none
  | _, lb, some xs, none => if lb then none else some xs
  | la, _, none, some ys => if la then none else some ys
  | _, _, none, none => none
termination_by structural _ _ ia _ => ia

def joinList : List (Flat A) → List (Flat A) → List (Flat A)
  | x :: xs, y :: ys => join x y :: joinList xs ys
  | _, _ => []
termination_by structural xs _ => xs

/-- The arguments of the values `C v` of `a` or `b`, from whether they may be any
    value `C v` (`xa`, `xb`), their constructors (`ta`, `tb`) and their arguments (`aa`,
    `ab`). A constructor gets any argument if one side may have any argument for it. -/
def joinArgs (xa xb : Bool) (ta tb : List String) :
    List (String × Flat A) → List (String × Flat A) → List (String × Flat A)
  | (c, x) :: xs, ys =>
    let rest := joinArgs xa xb ta tb xs ys
    match ys.lookup c with
    | some y => (c, join x y) :: rest
    | none => if xb || tb.contains c then rest else (c, x) :: rest
  | [], ys => ys.filter fun (c, _) => !(xa || ta.contains c)
termination_by structural xs _ => xs

end

theorem join_eq (a b : Flat A) :
    a.join b = { joinBase a b with
      elem := joinElem a.list b.list a.elem b.elem, items := joinItems a.list b.list a.items b.items,
      args := joinArgs a.ctor b.ctor a.ctors b.ctors a.args b.args } := by
  cases a
  cases b
  rfl

/-- The sites or constructors of `xs` that `b` also has: those of `ys`, or all of
    them if `any` (`b` may be any array or ref, or any constructor applied to an argument). -/
def common [BEq α] (xs ys : List α) (any : Bool) : List α :=
  xs.filter fun x => any || ys.contains x

/-- The values that both `a` and `b` describe. For the parts of lists and of ADT
    values, those of `a` if it has some, else those of `b`: they contain those of the
    meet. -/
def meet (a b : Flat A) : Flat A :=
  ⟨AbsDomain.meet a.int b.int, a.tt && b.tt, a.ff && b.ff, a.unit && b.unit,
   a.list && b.list, a.fn && b.fn, a.loc && b.loc, a.ctor && b.ctor,
   common a.refs b.refs b.loc ++ common b.refs [] (a.loc && !b.loc),
   common a.arrs b.arrs b.loc ++ common b.arrs [] (a.loc && !b.loc),
   common a.ctors b.ctors b.ctor ++ common b.ctors [] (a.ctor && !b.ctor),
   if a.list && b.list then (a.elem <|> b.elem) else none,
   if a.list && b.list then (a.items <|> b.items) else none,
   if a.args.isEmpty then b.args else a.args, a.empty && b.empty⟩

/-- `leq` without the parts of lists and of ADT values. -/
def leqBase (a b : Flat A) : Bool :=
  AbsDomain.leq a.int b.int && (!a.tt || b.tt) && (!a.ff || b.ff) && (!a.unit || b.unit) &&
  (!a.list || b.list) && (!a.fn || b.fn) && (!a.loc || b.loc) && (!a.ctor || b.ctor) &&
  (common a.refs b.refs b.loc).length == a.refs.length &&
  (common a.arrs b.arrs b.loc).length == a.arrs.length &&
  (common a.ctors b.ctors b.ctor).length == a.ctors.length

mutual

/-- `a` describes no more values than `b`. A site or a constructor of `a` must be in
    `b`, unless `b` may be any array or ref (`loc`), or any constructor (`ctor`). The
    parts of the lists and of the ADT values of `a` must be among those of `b`. -/
def leq : Flat A → Flat A → Bool
  | a@⟨_, _, _, _, la, _, _, _, _, _, ta, ea, ia, aa, na⟩,
    b@⟨_, _, _, _, _, _, _, _, _, _, _, eb, ib, ab, nb⟩ =>
    leqBase a b && (!la || ((!na || nb) && leqElem ea eb && leqItems ia ib)) &&
      leqArgs ab aa && ta.all fun c => (aa.lookup c).isSome || (ab.lookup c).isNone
termination_by structural a _ => a

def leqElem : Option (Flat A) → Option (Flat A) → Bool
  | _, none => true
  | some x, some y => leq x y
  | none, some _ => false
termination_by structural ea _ => ea

def leqItems : Option (List (Flat A)) → Option (List (Flat A)) → Bool
  | _, none => true
  | some xs, some ys => leqList xs ys
  | none, some _ => false
termination_by structural ia _ => ia

def leqList : List (Flat A) → List (Flat A) → Bool
  | x :: xs, y :: ys => leq x y && leqList xs ys
  | [], [] => true
  | _, _ => false
termination_by structural xs _ => xs

/-- Each argument of `aa` is in the argument of the same constructor in `ab`, if `ab`
    has one. -/
def leqArgs (ab : List (String × Flat A)) : List (String × Flat A) → Bool
  | (c, x) :: xs => (match ab.lookup c with | some y => leq x y | none => true) && leqArgs ab xs
  | [] => true
termination_by structural xs => xs

end

theorem leq_eq (a b : Flat A) :
    a.leq b = (leqBase a b &&
      (!a.list || ((!a.empty || b.empty) && leqElem a.elem b.elem && leqItems a.items b.items)) &&
      leqArgs b.args a.args && a.ctors.all fun c => (a.args.lookup c).isSome ||
        (b.args.lookup c).isNone) := by
  cases a
  cases b
  rfl

mutual

/-- Widening: the integers of `a` and `b` are widened, and so are the integers of their
    parts (`elem`, `items`, `args`). The other components are joined: they are finite. -/
def widen : Flat A → Flat A → Flat A
  | a@⟨ia, _, _, _, _, _, _, _, _, _, _, ea, isa, aa, _⟩, b =>
    let j := a.join b
    { j with
      int := AbsDomain.widen ia b.int, elem := widenOpt ea j.elem,
      items := widenItems isa j.items, args := widenArgs aa j.args }
termination_by structural a _ => a

def widenOpt : Option (Flat A) → Option (Flat A) → Option (Flat A)
  | some x, some y => some (widen x y)
  | _, y => y
termination_by structural ea _ => ea

def widenItems : Option (List (Flat A)) → Option (List (Flat A)) → Option (List (Flat A))
  | some xs, some ys => some (widenList xs ys)
  | _, ys => ys
termination_by structural ia _ => ia

def widenList : List (Flat A) → List (Flat A) → List (Flat A)
  | x :: xs, y :: ys => widen x y :: widenList xs ys
  | _, ys => ys
termination_by structural xs _ => xs

def widenArgs : List (String × Flat A) → List (String × Flat A) → List (String × Flat A)
  | (c, x) :: xs, js => widenArgs xs (js.map fun (d, y) => if d == c then (d, widen x y) else (d, y))
  | [], js => js
termination_by structural xs _ => xs

end

/-- `a`, with the parts deeper than `n` levels forgotten: any elements and any arguments.
    The inference uses it to keep its hints finite. -/
def trunc : Nat → Flat A → Flat A
  | 0, a => { a with elem := none, items := none, args := [] }
  | n + 1, a =>
    { a with elem := a.elem.map (trunc n), items := a.items.map (·.map (trunc n)),
             args := a.args.map fun (c, x) => (c, trunc n x) }

/-- Concretisation: the values `a` describes. -/
def mem (a : Flat A) : Value → Prop
  | .int n => γ a.int n
  | .bool true => a.tt = true
  | .bool false => a.ff = true
  | .unit => a.unit = true
  | .nil | .cons _ _ => a.list = true
  | .clos .. => a.fn = true
  | .arr _ | .ref _ => a.loc = true
  | .ctor _ _ => a.ctor = true

theorem not_mem_bot {v : Value} : ¬ (bot : Flat A).mem v := by
  intro h
  cases v
  case int n => exact bot_sound n h
  case bool b => cases b <;> simp [mem, bot] at h
  all_goals simp [mem, bot] at h

theorem mem_top (v : Value) : (top : Flat A).mem v := by
  cases v
  case int n => exact top_sound n
  case bool b => cases b <;> rfl
  all_goals rfl

theorem mem_join_l {a b : Flat A} {v : Value} (h : a.mem v) : (a.join b).mem v := by
  rw [join_eq]
  cases v
  case int n => exact join_sound_l h
  case bool c => cases c <;> simp_all [mem, joinBase]
  all_goals simp_all [mem, joinBase]

theorem mem_join_r {a b : Flat A} {v : Value} (h : b.mem v) : (a.join b).mem v := by
  rw [join_eq]
  cases v
  case int n => exact join_sound_r h
  case bool c => cases c <;> simp_all [mem, joinBase]
  all_goals simp_all [mem, joinBase]

/-- `a ≤ b` gives `a.int ≤ b.int`. -/
theorem leq_int {a b : Flat A} (hl : a.leq b = true) : AbsDomain.leq a.int b.int = true := by
  simp only [leq_eq, leqBase, Bool.and_eq_true] at hl
  simp_all

theorem mem_leq {a b : Flat A} {v : Value} (h : a.mem v) (hl : a.leq b = true) : b.mem v := by
  cases v
  case int n => exact leq_sound h (leq_int hl)
  all_goals simp only [leq_eq, leqBase, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hl
  case bool c => cases c <;> simp_all [mem]
  all_goals simp_all [mem]

/-- `a` describes no more values than `b`. -/
def sub (a b : Flat A) : Prop := ∀ v, a.mem v → b.mem v

theorem sub_refl (a : Flat A) : a.sub a := fun _ h => h

/-- `v` is a list whose elements are all in `e`. -/
def listMem (e : Flat A) : Value → Prop
  | .nil => True
  | .cons h t => e.mem h ∧ e.listMem t
  | _ => False

theorem listMem_mono {e e' : Flat A} (he : e.sub e') :
    (v : Value) → e.listMem v → e'.listMem v
  | .nil, _ => trivial
  | .cons h t, ⟨hh, ht⟩ => ⟨he h hh, listMem_mono he t ht⟩

theorem listMem_isList {e : Flat A} : (v : Value) → e.listMem v → v.isList = true
  | .nil, _ | .cons _ _, _ => rfl

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

/-- `a` printed, with its parts down to `n` levels: `list of e`, `[a; b]` for lists of a
    known length, `(a, b)` for a tuple, and `C x` for a constructor with its argument. -/
def str [ToString A] : Nat → Flat A → String
  | n, a =>
    if top.leq a then "⊤" else
    let sub (x : Flat A) : String := match n with
      | 0 => "..."
      | k + 1 => str k x
    let lists :=
      match a.list, a.items, a.elem with
      | false, _, _ => []
      | true, some ws, _ => [s!"[{"; ".intercalate (ws.map sub)}]"]
      | true, none, some e => [s!"{if a.empty then "" else "non-empty "}list of {sub e}"]
      | true, none, none => [if a.empty then "list" else "non-empty list"]
    let tag (c : String) : String :=
      match a.args.lookup c with
      -- a constructor without argument has the argument `()`
      | some x => if x.leq unitV then c else
        match c.startsWith "%", x.items with
        | true, some ws => s!"({", ".intercalate (ws.map sub)})"
        | _, _ => s!"{c} {sub x}"
      | none => c
    let parts :=
      (if AbsDomain.leq a.int AbsDomain.bot then [] else [toString a.int]) ++
      (match a.tt, a.ff with
        | true, true => ["bool"] | true, false => ["true"]
        | false, true => ["false"] | false, false => []) ++
      (if a.unit then ["()"] else []) ++ lists ++
      (if a.fn then ["fun"] else []) ++ (if a.loc then ["loc"] else []) ++
      (if a.ctor then ["ctor"] else []) ++
      a.refs.map (s!"ref !{·}") ++ a.arrs.map (s!"array !{·}") ++ a.ctors.map tag
    if parts.isEmpty then "⊥" else " | ".intercalate parts

instance [ToString A] : ToString (Flat A) where
  toString := str 4

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
  /-- The exceptions the call may raise, for the analysis of exceptions (see `aevalM`).
      With this analysis, `fails` says only whether the call may stop with an error that
      isn't an exception. The proofs don't use `raises`. -/
  raises : Flat A
  deriving Inhabited

/-- The closure `clos s x b ρ` satisfies the summary `S`, when `S.rest` is empty. -/
def Sat [NumDomain A] (S : Summary A) (s : Option String) (x : String) (b : Expr)
    (ρ : Env) : Prop :=
  ∀ v w μ μ', S.pre.mem v → Eval (callEnv s x b ρ v) μ b (.ok w) μ' → S.res.mem w

/-- `Flat`, plus a summary that the closures it may be satisfy (`fn`: any closure),
    and a description of the elements of the lists it may be (`list`: any list).
    The lists described by `elems` may be `[]` only if `mayNil` is `true`. -/
structure AVal (A : Type) extends Flat A where
  sum : Option (Summary A)
  elems : Option (Flat A) := none
  mayNil : Bool := true
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
def ctorV : AVal A := ofFlat Flat.ctorV
/-- The closures that satisfy `S`. -/
def summary (S : Summary A) : AVal A := { toFlat := Flat.bot, sum := some S }
/-- The lists whose elements are in `e`, and that may be `[]` only if `mayNil`. -/
def listOf (e : Flat A) (mayNil : Bool := true) : AVal A :=
  { toFlat := Flat.bot, sum := none, elems := some e, mayNil := mayNil }

/-- Forget the summary and the elements: "any closure" and "any list". -/
def flat (a : AVal A) : Flat A :=
  let elem := flatElem a
  { a.toFlat with
    fn := a.fn || a.sum.isSome, list := a.list || a.elems.isSome, elem,
    empty := (a.list && a.toFlat.empty) || (a.elems.isSome && a.mayNil) }
where
  /-- The elements of the lists of `a`, for `Flat.elem`: those of `a.toFlat` and of
      `a.elems`. -/
  flatElem (a : AVal A) : Option (Flat A) :=
    match a.list, a.toFlat.elem, a.elems with
    | true, none, _ => none
    | true, some x, some e => some (x.join e)
    | true, some x, none => some x
    | false, _, e => e

/-- Summaries are kept when they have the same preconditions, forgotten otherwise.
    Elements are joined. The lists may be `[]` if those of `a` or of `b` may. -/
def join (a b : AVal A) : AVal A :=
  { joinSum a b with
    elems := Option.merge Flat.join a.elems b.elems,
    mayNil := (a.elems.isSome && a.mayNil) || (b.elems.isSome && b.mayNil),
    items := joinItems a b }
where
  /-- The lists of `a` and `b`, element by element (`Flat.items`): kept if `a` and `b`
      give them with the same length, or if only one of them may be a list. -/
  joinItems (a b : AVal A) : Option (List (Flat A)) :=
    match a.items, b.items with
    | some xs, some ys => if xs.length == ys.length then some (xs.zipWith Flat.join ys) else none
    | some xs, none => if b.list || b.elems.isSome then none else some xs
    | none, some ys => if a.list || a.elems.isSome then none else some ys
    | none, none => none
  joinSum (a b : AVal A) : AVal A :=
  match a.sum, b.sum with
  | some S, some T =>
    if S.pre.leq T.pre && T.pre.leq S.pre && Flat.leqs S.rest T.rest &&
        Flat.leqs T.rest S.rest then
      { toFlat := a.toFlat.join b.toFlat,
        sum := some ⟨S.pre, S.rest, S.res.join T.res, S.fails || T.fails,
          S.raises.join T.raises⟩ }
    else ofFlat (a.flat.join b.flat)
  | some S, none => { toFlat := a.toFlat.join b.toFlat, sum := some S }
  | none, s => { toFlat := a.toFlat.join b.toFlat, sum := s }

/-! ### Lists -/

/-- `h :: t`: the elements of `t`, and `h`. If `t` may be any list, any list. -/
def cons (h t : AVal A) : AVal A :=
  if t.list then listV
  else match t.elems with
    | some e => listOf (e.join h.flat) (mayNil := false)
    | none => bot   -- `t` is not a list: an error, no value

/-- `a` may be `[]`. -/
def mayBeNil (a : AVal A) : Bool := a.list || (a.elems.isSome && a.mayNil)

/-- The first elements of the lists `a` describes. -/
def heads (a : AVal A) : Flat A :=
  if a.list then Flat.top else a.elems.getD Flat.bot

/-- The tails of the lists `a` describes. If `a` may be any list, `top`: a `Value.cons`
    may have a tail that is not a list. -/
def tails (a : AVal A) : AVal A :=
  if a.list then top else (a.elems.map fun e => listOf e).getD bot

/-! ### Lists of a known length (for the analysis of tuples, see `aevalM`) -/

/-- The lists `[v₁; ...; vₙ]` where each `vᵢ` is in the `i`-th element of `ws`. -/
def itemsOf (ws : List (Flat A)) : AVal A :=
  { listOf (ws.foldl Flat.join Flat.bot) (mayNil := ws.isEmpty) with items := some ws }

/-- `h :: t`, element by element if `t` is known that way. If `t` may be any list, the
    lists whose elements are those of `t` (`Flat.elem`) and `h`. -/
def consI (h t : AVal A) : AVal A :=
  if t.list then
    match t.flat.elem with
    | some e => ofFlat { Flat.listV with elem := some (e.join h.flat), empty := false }
    | none => ofFlat { Flat.listV with empty := false }
  else { cons h t with items := t.items.map (h.flat :: ·) }

/-- `mayBeNil`, using `items` if `a` has them, and `Flat.empty` if it may be any list. -/
def mayBeNilI (a : AVal A) : Bool :=
  match a.items with
  | some ws => ws.isEmpty
  | none => (a.list && a.toFlat.empty) || (a.elems.isSome && a.mayNil)

/-- `heads`, using `items` if `a` has them, and the elements of `a.toFlat` if it may be
    any list. -/
def headsI (a : AVal A) : Flat A :=
  match a.items with
  | some (w :: _) => w
  | some [] => Flat.bot
  | none =>
    if a.list then
      (a.toFlat.elem.getD Flat.top).join (a.elems.getD Flat.bot)
    else a.heads

/-- `tails`, using `items` if `a` has them. The tails of lists are lists, with the same
    elements: `Eval` only builds a `::` whose tail is a list (`Semantics.lean`). -/
def tailsI (a : AVal A) : AVal A :=
  match a.items with
  | some (_ :: ws) => itemsOf ws
  | some [] => bot
  | none =>
    if a.list then
      (ofFlat { Flat.listV with elem := a.toFlat.elem }).join ((a.elems.map (listOf ·)).getD bot)
    else a.tails

instance [ToString A] : ToString (AVal A) where
  toString a :=
    let parts :=
      (if toString a.toFlat == "⊥" then [] else [toString a.toFlat]) ++
      (match a.sum with
        | none => []
        | some S => [s!"fun {" -> ".intercalate ((S.pre :: S.rest).map toString)} -> {S.res}"]) ++
      (match a.items, a.elems with
        | some ws, _ => [s!"[{"; ".intercalate (ws.map toString)}]"]
        | none, none => []
        | none, some e => [if a.mayNil then s!"list of {e}" else s!"non-empty list of {e}"])
    if parts.isEmpty then "⊥" else " | ".intercalate parts

end AVal

end Diva.AbsInt
