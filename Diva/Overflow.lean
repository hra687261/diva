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

/-- `e` with a check after each operation that may overflow `t`. `l` has the positions
    of `e`. The code of a check has the positions of its operation. -/
def check (t : IntType) : Expr → Loc → LExpr
  | .binop op a b, l =>
    let a := check t a (l.kid 0)
    let b := check t b (l.kid 1)
    let e := Expr.binop op a.expr b.expr
    let el := Loc.node l.span [a.loc, b.loc]
    if mayOverflow op then
      let g := Loc.leaf l.span
      ⟨.letin res e (.letin "_" (.assert (inRange t)) (.var res)),
       .node l.span [el, .node l.span [.node l.span [g], g]]⟩
    else ⟨e, el⟩
  | .app f a, l =>
    let f := check t f (l.kid 0)
    let a := check t a (l.kid 1)
    ⟨.app f.expr a.expr, .node l.span [f.loc, a.loc]⟩
  | .lam x b, l =>
    let b := check t b (l.kid 0)
    ⟨.lam x b.expr, .node l.span [b.loc]⟩
  | .letin x a b, l =>
    let a := check t a (l.kid 0)
    let b := check t b (l.kid 1)
    ⟨.letin x a.expr b.expr, .node l.span [a.loc, b.loc]⟩
  | .letrec f x b e2, l =>
    let b := check t b (l.kid 0)
    let e2 := check t e2 (l.kid 1)
    ⟨.letrec f x b.expr e2.expr, .node l.span [b.loc, e2.loc]⟩
  | .ite c a b, l =>
    let c := check t c (l.kid 0)
    let a := check t a (l.kid 1)
    let b := check t b (l.kid 2)
    ⟨.ite c.expr a.expr b.expr, .node l.span [c.loc, a.loc, b.loc]⟩
  | .cons a b, l =>
    let a := check t a (l.kid 0)
    let b := check t b (l.kid 1)
    ⟨.cons a.expr b.expr, .node l.span [a.loc, b.loc]⟩
  | .matchList s n x xs c, l =>
    let s := check t s (l.kid 0)
    let n := check t n (l.kid 1)
    let c := check t c (l.kid 2)
    ⟨.matchList s.expr n.expr x xs c.expr, .node l.span [s.loc, n.loc, c.loc]⟩
  | .assert c, l =>
    let c := check t c (l.kid 0)
    ⟨.assert c.expr, .node l.span [c.loc]⟩
  | .alloc site n v, l =>
    let n := check t n (l.kid 0)
    let v := check t v (l.kid 1)
    ⟨.alloc site n.expr v.expr, .node l.span [n.loc, v.loc]⟩
  | .get a i, l =>
    let a := check t a (l.kid 0)
    let i := check t i (l.kid 1)
    ⟨.get a.expr i.expr, .node l.span [a.loc, i.loc]⟩
  | .set a i v, l =>
    let a := check t a (l.kid 0)
    let i := check t i (l.kid 1)
    let v := check t v (l.kid 2)
    ⟨.set a.expr i.expr v.expr, .node l.span [a.loc, i.loc, v.loc]⟩
  | .len a, l =>
    let a := check t a (l.kid 0)
    ⟨.len a.expr, .node l.span [a.loc]⟩
  | .ref site v, l =>
    let v := check t v (l.kid 0)
    ⟨.ref site v.expr, .node l.span [v.loc]⟩
  | .deref r, l =>
    let r := check t r (l.kid 0)
    ⟨.deref r.expr, .node l.span [r.loc]⟩
  | .assign r v, l =>
    let r := check t r (l.kid 0)
    let v := check t v (l.kid 1)
    ⟨.assign r.expr v.expr, .node l.span [r.loc, v.loc]⟩
  | .exn c v, l =>
    let v := check t v (l.kid 0)
    ⟨.exn c v.expr, .node l.span [v.loc]⟩
  | .raise v, l =>
    let v := check t v (l.kid 0)
    ⟨.raise v.expr, .node l.span [v.loc]⟩
  | .tryw a k h, l =>
    let a := check t a (l.kid 0)
    let h := check t h (l.kid 1)
    ⟨.tryw a.expr k h.expr, .node l.span [a.loc, h.loc]⟩
  | .exnCase s c x h m, l =>
    let s := check t s (l.kid 0)
    let h := check t h (l.kid 1)
    let m := check t m (l.kid 2)
    ⟨.exnCase s.expr c x h.expr m.expr, .node l.span [s.loc, h.loc, m.loc]⟩
  | e@(.int _), l | e@(.bool _), l | e@.unit, l | e@(.var _), l | e@.nil, l => ⟨e, l⟩

/-- A top-level item, with a check after each operation that may overflow `t`. -/
def item (t : IntType) : Item × Loc → Item × Loc
  | (.decl (.val f e) sp, l) =>
    let e := check t e l
    (.decl (.val f e.expr) sp, e.loc)
  | (.decl (.recFn f x e) sp, l) =>
    let e := check t e l
    (.decl (.recFn f x e.expr) sp, e.loc)
  | (.expr e, l) =>
    let e := check t e l
    (.expr e.expr, e.loc)

/-- The items `is`, with the checks for the integer type `intTy` (none without one). -/
def items (intTy : Option IntType) (is : List (Item × Loc)) : List (Item × Loc) :=
  match intTy with
  | none => is
  | some t => is.map (item t)

/-- The number of bits of the integer type, if `e` is a check that `check` adds:
    `let %r = a op b in assert (min <= %r && %r <= max); %r`. -/
def bits? : Expr → Option Nat
  | .letin r (.binop op _ _)
      (.letin "_" (.assert (.ite (.binop .le (.int lo) (.var r1)) (.binop .le (.var r2) (.int hi))
        (.bool false))) (.var r3)) =>
    if r == res && r1 == res && r2 == res && r3 == res && mayOverflow op && 0 ≤ hi &&
        lo == -(hi + 1) then
      some ((hi + 1).toNat.log2 + 1)
    else none
  | _ => none

end Overflow

end Diva
