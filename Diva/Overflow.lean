import Diva.Loc

/-!
# Overflow checks (untrusted)

In DIVA's semantics (`Eval`), integers have no bound. But most programming
languages use machine integers, which have a fixed number of bits, and usually
wrap around on overflow.

With an integer type `t` (`IntType`), each `+`, `-`, `*` and `/` checks that its result
fits in `t`: `a + b` becomes

```
let %r = a + b in assert (t.min <= %r && %r <= t.max); %r
```

So a program that DIVA proves never fails never overflows, and its results are those
of `t`. `mod` never overflows. `/` overflows only for `t.min / -1`. Contracts keep
integers without bound.
-/

namespace Diva

/-- A type of integers with `bits` bits (at least 1): the integers from `-2^(bits-1)`
    to `2^(bits-1) - 1`. -/
structure IntType where
  bits : Nat
  deriving Inhabited, BEq, Repr

namespace IntType

def int63 : IntType := ⟨63⟩
def int32 : IntType := ⟨32⟩
def int64 : IntType := ⟨64⟩

/-- The smallest integer of `t`. -/
def min (t : IntType) : Int := -((2 ^ (t.bits - 1) : Nat) : Int)
/-- The largest integer of `t`. -/
def max (t : IntType) : Int := (2 ^ (t.bits - 1) : Nat) - 1

end IntType

namespace Overflow

/-- The result of `op` may not fit in an integer type: `op` is `+`, `-`, `*` or `/`. -/
def mayOverflow : BinOp → Bool
  | .add | .sub | .mul | .div => true
  | _ => false

/-- The name of the result in a check. A name that starts with `%` can't be written in
    a program, so it hides no name of the program. -/
def res : String := "%r"

/-- `t.min <= %r && %r <= t.max` -/
def inRange (t : IntType) : Expr :=
  .ite (.binop .le (.int t.min) (.var res)) (.binop .le (.var res) (.int t.max)) (.bool false)

/-- `e`, followed by the check that its value fits in `t`:
    `let %r = e in assert (t.min <= %r && %r <= t.max); %r`. The code of the check has
    the span `sp`. -/
def wrap (t : IntType) (e : LExpr) (sp : Span) : LExpr :=
  let g := Loc.leaf sp
  ⟨.letin res e.expr (.letin "_" (.assert (inRange t)) (.var res)),
   .node sp [e.loc, .node sp [.node sp [g], g]]⟩

/-- `e` with a check after each operation that may overflow `t`. `l` has the positions
    of `e`. The code of a check has the positions of its operation. An integer literal
    that doesn't fit in `t` is an error, with its position. `-n`, which the parser reads
    as `0 - n`, may be `t.min`: `n` may be `t.max + 1`. -/
def check (t : IntType) : Expr → Loc → Except (Int × Span) LExpr
  | .int n, l => if t.min ≤ n && n ≤ t.max then pure ⟨.int n, l⟩ else throw (n, l.span)
  | .binop op a b, l => do
    let a ← check t a (l.kid 0)
    let b ← match op, a.expr, b with
      | .sub, .int 0, .int n => if n == t.max + 1 then pure ⟨.int n, l.kid 1⟩ else check t b (l.kid 1)
      | _, _, _ => check t b (l.kid 1)
    let e : LExpr := ⟨.binop op a.expr b.expr, .node l.span [a.loc, b.loc]⟩
    return if mayOverflow op then wrap t e l.span else e
  | .app f a, l => do
    let f ← check t f (l.kid 0)
    let a ← check t a (l.kid 1)
    return ⟨.app f.expr a.expr, .node l.span [f.loc, a.loc]⟩
  | .lam x b, l => do
    let b ← check t b (l.kid 0)
    return ⟨.lam x b.expr, .node l.span [b.loc]⟩
  | .letin x a b, l => do
    let a ← check t a (l.kid 0)
    let b ← check t b (l.kid 1)
    return ⟨.letin x a.expr b.expr, .node l.span [a.loc, b.loc]⟩
  | .letrec f x b e2, l => do
    let b ← check t b (l.kid 0)
    let e2 ← check t e2 (l.kid 1)
    return ⟨.letrec f x b.expr e2.expr, .node l.span [b.loc, e2.loc]⟩
  | .ite c a b, l => do
    let c ← check t c (l.kid 0)
    let a ← check t a (l.kid 1)
    let b ← check t b (l.kid 2)
    return ⟨.ite c.expr a.expr b.expr, .node l.span [c.loc, a.loc, b.loc]⟩
  | .cons a b, l => do
    let a ← check t a (l.kid 0)
    let b ← check t b (l.kid 1)
    return ⟨.cons a.expr b.expr, .node l.span [a.loc, b.loc]⟩
  | .matchList s n x xs c, l => do
    let s ← check t s (l.kid 0)
    let n ← check t n (l.kid 1)
    let c ← check t c (l.kid 2)
    return ⟨.matchList s.expr n.expr x xs c.expr, .node l.span [s.loc, n.loc, c.loc]⟩
  | .assert c, l => do
    let c ← check t c (l.kid 0)
    return ⟨.assert c.expr, .node l.span [c.loc]⟩
  | .alloc site n v, l => do
    let n ← check t n (l.kid 0)
    let v ← check t v (l.kid 1)
    return ⟨.alloc site n.expr v.expr, .node l.span [n.loc, v.loc]⟩
  | .get a i, l => do
    let a ← check t a (l.kid 0)
    let i ← check t i (l.kid 1)
    return ⟨.get a.expr i.expr, .node l.span [a.loc, i.loc]⟩
  | .set a i v, l => do
    let a ← check t a (l.kid 0)
    let i ← check t i (l.kid 1)
    let v ← check t v (l.kid 2)
    return ⟨.set a.expr i.expr v.expr, .node l.span [a.loc, i.loc, v.loc]⟩
  | .len a, l => do
    let a ← check t a (l.kid 0)
    return ⟨.len a.expr, .node l.span [a.loc]⟩
  | .listLen a, l => do
    let a ← check t a (l.kid 0)
    return ⟨.listLen a.expr, .node l.span [a.loc]⟩
  | .ref site v, l => do
    let v ← check t v (l.kid 0)
    return ⟨.ref site v.expr, .node l.span [v.loc]⟩
  | .deref r, l => do
    let r ← check t r (l.kid 0)
    return ⟨.deref r.expr, .node l.span [r.loc]⟩
  | .assign r v, l => do
    let r ← check t r (l.kid 0)
    let v ← check t v (l.kid 1)
    return ⟨.assign r.expr v.expr, .node l.span [r.loc, v.loc]⟩
  | .ctor c v, l => do
    let v ← check t v (l.kid 0)
    return ⟨.ctor c v.expr, .node l.span [v.loc]⟩
  | .raise v, l => do
    let v ← check t v (l.kid 0)
    return ⟨.raise v.expr, .node l.span [v.loc]⟩
  | .tryw a k h, l => do
    let a ← check t a (l.kid 0)
    let h ← check t h (l.kid 1)
    return ⟨.tryw a.expr k h.expr, .node l.span [a.loc, h.loc]⟩
  | .ctorCase s c x h m, l => do
    let s ← check t s (l.kid 0)
    let h ← check t h (l.kid 1)
    let m ← check t m (l.kid 2)
    return ⟨.ctorCase s.expr c x h.expr m.expr, .node l.span [s.loc, h.loc, m.loc]⟩
  | e@(.bool _), l | e@.unit, l | e@(.var _), l | e@.nil, l => pure ⟨e, l⟩

/-- A top-level item, with a check after each operation that may overflow `t`. -/
def item (t : IntType) : Item × Loc → Except (Int × Span) (Item × Loc)
  | (.decl (.val f e) sp, l) => do
    let e ← check t e l
    return (.decl (.val f e.expr) sp, e.loc)
  | (.decl (.recFn f x e) sp, l) => do
    let e ← check t e l
    return (.decl (.recFn f x e.expr) sp, e.loc)
  | (.expr e, l) => do
    let e ← check t e l
    return (.expr e.expr, e.loc)

/-- The items `is` of the program `src`, with the checks for the integer type `intTy`
    (none without one). An integer literal that doesn't fit is an error, with its line
    and column in `src`. -/
def items (intTy : Option IntType) (src : String) (is : List (Item × Loc)) :
    Except String (List (Item × Loc)) :=
  match intTy with
  | none => .ok is
  | some t =>
    match is.mapM (item t) with
    | .ok is => .ok is
    | .error (n, sp) =>
      let (l, c) := lineCol src sp.start
      .error s!"{l}:{c}: the integer {n} doesn't fit in {t.bits}-bit integers"

/-- The number of bits of the integer type, if `e` is a check that `wrap` gives:
    `let %r = e1 in assert (min <= %r && %r <= max); %r`. -/
def bits? : Expr → Option Nat
  | .letin r _
      (.letin "_" (.assert (.ite (.binop .le (.int lo) (.var r1)) (.binop .le (.var r2) (.int hi))
        (.bool false))) (.var r3)) =>
    if r == res && r1 == res && r2 == res && r3 == res && 0 ≤ hi && lo == -(hi + 1) then
      some ((hi + 1).toNat.log2 + 1)
    else none
  | _ => none

end Overflow

end Diva
