import Diva.AbsInt.Infer

/-!
# The optimiser

`opt H E σ e` rewrites `e` using the facts of the analysis, in an abstract environment
`σ` describing the values of the free variables of `e`.

Constant folding: an expression that is pure (`Expr.pure`: it terminates and
doesn't change the store), that can't fail (`mayFail`), and whose value the
analysis knows exactly, becomes that value.

Dead branches: `if c then t else e`, where `c` is pure, can't fail and is
certainly `true`, becomes `t` (and `e` if `c` is certainly `false`).

Proved assertions: `assert c`, where `c` is pure, can't fail and is certainly
`true`, becomes `()`.

Unused names: `let x = e1 in e2` becomes `e2` when `e1` is pure, can't fail, and the
optimised `e2` doesn't use `x`. For example, `assert c; e2` becomes `e2` when `c` is
certainly `true`.

Erased checks: with `E`, when `c` is a check (`Expr.isCheck`), `assert c` becomes `()`,
and `assert c; e2` becomes `e2`. This is correct only for a program that never fails:
then `c` gives `true` whenever it is run.

Identities: `a + 0`, `a - 0`, `a * 1` and `a / 1` become `a`, and `0 + b` and `1 * b`
become `b`. The dropped side must be pure, can't fail and be certainly that integer.
-- TODO: this should ideally use type information to determine neutral values etc

A function's body is optimised with its parameter at `⊤`, not at the hint for the
parameter. A hint is only checked at the calls the analysis sees, and a closure may
be called from anywhere.

`optimize_correct` (`OptSound.lean`) states that the result is equivalent.
-/

namespace Diva.Opt

open AbsInt AbsDomain

variable {A : Type} [NumDomain A]

/-- The literal of the only value `a` describes, if `a` describes exactly one
    integer or one boolean. -/
def literal (a : AVal A) : Option Expr :=
  if a.sum.isSome || a.elems.isSome then none
  else match NumDomain.asConst a.int with
    | some n => if a.toFlat.leq (Flat.ofInt a.int) then some (.int n) else none
    | none =>
      if a.toFlat.leq (Flat.bools true false) && a.tt then some (.bool true)
      else if a.toFlat.leq (Flat.bools false true) && a.ff then some (.bool false)
      else none

/-- The literal `e` certainly evaluates to, if `e` is pure, can't fail, and the
    analysis knows its value exactly. -/
def constOf (H : Hints A) (σ : AEnv A) (e : Expr) : Option Expr :=
  if e.pure && !mayFail H σ e then literal (aeval H σ e) else none

/-- The integer `n` such that `x op n = x` for every integer `x`. -/
def _root_.Diva.BinOp.rightUnit : BinOp → Option Int
  | .add | .sub => some 0
  | .mul | .div => some 1
  | _ => none

/-- The integer `n` such that `n op x = x` for every integer `x`. -/
def _root_.Diva.BinOp.leftUnit : BinOp → Option Int
  | .add => some 0
  | .mul => some 1
  | _ => none

/-- `e` is certainly the integer `n` (`constOf` gives `n`). -/
def isInt (H : Hints A) (σ : AEnv A) (e : Expr) (n : Int) : Bool :=
  match constOf H σ e with
  | some (.int m) => m == n
  | _ => false

/-- `a op b` gives what `a` gives: `b` is certainly `op`'s right unit, and `a op b`
    can't fail (so `a` gives an integer). -/
def rightIdentity (H : Hints A) (σ : AEnv A) (op : BinOp) (a b : Expr) : Bool :=
  match op.rightUnit with
  | some n => !mayFail H σ (.binop op a b) && isInt H σ b n
  | none => false

/-- `a op b` gives what `b` gives: `a` is certainly `op`'s left unit, and `a op b`
    can't fail (so `b` gives an integer). -/
def leftIdentity (H : Hints A) (σ : AEnv A) (op : BinOp) (a b : Expr) : Bool :=
  match op.leftUnit with
  | some n => !mayFail H σ (.binop op a b) && isInt H σ a n
  | none => false

/-- The abstract environment of the body of `fun x -> b`, or of `let rec f x = b`
    (`s = some f`): `x` at `⊤`, and `f` as `aeval` gives it. -/
def bodyEnv (H : Hints A) (σ : AEnv A) (s : Option String) (x : String) (b : Expr) :
    AEnv A :=
  match s with
  | none => (x, AVal.top) :: σ
  | some f => (x, AVal.top) :: (f, letrecVal H σ f x b) :: σ

/-- `e` is a check: made of literals, names, operators and `if`. A check finishes,
    doesn't change the store, and its errors are not exceptions. -/
def _root_.Diva.Expr.isCheck : Expr → Bool
  | .int _ | .bool _ | .unit | .var _ | .nil => true
  | .binop _ a b => a.isCheck && b.isCheck
  | .ite c t e => c.isCheck && t.isCheck && e.isCheck
  | _ => false

/-- The errors of `e` are fatal: `e` is a check, or `assert c` where `c` is a check. -/
def _root_.Diva.Expr.onlyFatal : Expr → Bool
  | .assert c => c.isCheck
  | e => e.isCheck

/-- The abstract environment after `e1` in `let x = e1 in e2`. After `assert c`, the
    condition `c` holds: otherwise the run has already failed. So `c` narrows `σ`, as
    in the `then` branch of an `if`. `assert c; e2` is `let _ = assert c in e2`. -/
def afterAssert (σ : AEnv A) : Expr → AEnv A
  | .assert c => (σ.assume c true).getD σ
  | _ => σ

/-- `e` optimised. The environments are those of `aeval`, except for function
    bodies (`bodyEnv`). With `E` (erase), every `assert c` where `c` is a check
    (`Expr.isCheck`) becomes `()`. This is correct only for a program that never fails
    (`opt_erase_correct`). -/
def opt (H : Hints A) (E : Bool) (σ : AEnv A) (e : Expr) : Expr :=
  match constOf H σ e with
  | some c => c
  | none =>
    match e with
    | .lam x b => .lam x (opt H E (bodyEnv H σ none x b) b)
    | .letrec f x b e2 =>
      .letrec f x (opt H E (bodyEnv H σ (some f) x b) b)
        (opt H E ((f, letrecVal H σ f x b) :: σ) e2)
    | .app f a => .app (opt H E σ f) (opt H E σ a)
    | .letin x e1 e2 =>
      let e1' := opt H E σ e1
      let e2' := opt H E ((x, aeval H σ e1) :: afterAssert σ e1) e2
      -- `e1` finishes, doesn't change the store and can't fail, and `e2'` doesn't use `x`.
      -- With `E`, the program never fails, so an `e1` whose errors are fatal can't fail.
      if e1.pure && (!mayFail H σ e1 || E && e1.onlyFatal) &&
          !(freeNames [] e2').contains x then e2'
      else .letin x e1' e2'
    | .binop op a b =>
      -- `a + 0`, `a - 0`, `a * 1`, `a / 1` become `a`, and `0 + b`, `1 * b` become `b`
      if rightIdentity H σ op a b then opt H E σ a
      else if leftIdentity H σ op a b then opt H E σ b
      else .binop op (opt H E σ a) (opt H E σ b)
    | .cons a b => .cons (opt H E σ a) (opt H E σ b)
    | .ite c t e =>
      match constOf H σ c with
      -- if the condition is certainly `true` only the `then` branch remains
      | some (.bool true) => opt H E ((σ.assume c true).getD σ) t
      | some (.bool false) => opt H E ((σ.assume c false).getD σ) e
      | _ =>
        -- each branch, knowing the condition (`σ` if the branch can't be taken)
        .ite (opt H E σ c) (opt H E ((σ.assume c true).getD σ) t)
          (opt H E ((σ.assume c false).getD σ) e)
    | .matchList s n x xs c =>
      let vs := aeval H σ s
      .matchList (opt H E σ s) (opt H E σ n) x xs
        (opt H E ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c)
    | .assert c =>
      -- with `E`, the program never fails, so a check that it runs gives `true`
      if E && c.isCheck then .unit
      else
      match constOf H σ c with
      -- the assertion certainly holds
      | some (.bool true) => .unit
      | _ => .assert (opt H E σ c)
    | .alloc site n v => .alloc site (opt H E σ n) (opt H E σ v)
    | .get a i => .get (opt H E σ a) (opt H E σ i)
    | .set a i v => .set (opt H E σ a) (opt H E σ i) (opt H E σ v)
    | .len a => .len (opt H E σ a)
    | .ref site v => .ref site (opt H E σ v)
    | .deref r => .deref (opt H E σ r)
    | .assign r v => .assign (opt H E σ r) (opt H E σ v)
    | .ctor t v => .ctor t (opt H E σ v)
    | .raise v => .raise (opt H E σ v)
    | .tryw a k h => .tryw (opt H E σ a) k (opt H E ((k, AVal.top) :: σ) h)
    | .ctorCase s t x h m => .ctorCase (opt H E σ s) t x (opt H E ((x, AVal.top) :: σ) h) (opt H E σ m)
    | e => e

/-- A program optimised, with the hints inferred for it. `σ` describes its free
    variables. -/
def optimize (σ : AEnv A) (e : Expr) (E : Bool := false) : Expr := opt (inferHints σ e) E σ e

end Diva.Opt
