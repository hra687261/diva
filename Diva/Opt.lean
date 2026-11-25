import Diva.AbsInt.Infer

/-!
# The optimiser

`opt H σ e` rewrites `e` using the facts of the analysis, in an abstract environment
`σ` describing the values of the free variables of `e`.

Constant folding: an expression that is pure (`Expr.pure`: it terminates and
doesn't change the store), that can't fail (`mayFail`), and whose value the
analysis knows exactly, becomes that value.

Dead branches: `if c then t else e`, where `c` is pure, can't fail and is
certainly `true`, becomes `t` (and `e` if `c` is certainly `false`).

Proved assertions: `assert c`, where `c` is pure, can't fail and is certainly
`true`, becomes `()`.

Unused names: `let x = e1 in e2` becomes `e2` when `e1` is pure, can't fail, and the
optimised `e2` doesn't use `x`. For example, `let _ = () in e2`, which is
left by a proved `assert`, becomes `e2`.

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

/-- The abstract environment after `e1` in `let x = e1 in e2`. After `assert c`, the
    condition `c` holds: otherwise the run has already failed. So `c` narrows `σ`, as
    in the `then` branch of an `if`. `assert c; e2` is `let _ = assert c in e2`. -/
def afterAssert (σ : AEnv A) : Expr → AEnv A
  | .assert c => (σ.assume c true).getD σ
  | _ => σ

/-- `e` optimised. The environments are those of `aeval`, except for function
    bodies (`bodyEnv`). -/
def opt (H : Hints A) (σ : AEnv A) (e : Expr) : Expr :=
  match constOf H σ e with
  | some c => c
  | none =>
    match e with
    | .lam x b => .lam x (opt H (bodyEnv H σ none x b) b)
    | .letrec f x b e2 =>
      .letrec f x (opt H (bodyEnv H σ (some f) x b) b)
        (opt H ((f, letrecVal H σ f x b) :: σ) e2)
    | .app f a => .app (opt H σ f) (opt H σ a)
    | .letin x e1 e2 =>
      let e1' := opt H σ e1
      let e2' := opt H ((x, aeval H σ e1) :: afterAssert σ e1) e2
      -- `e1` finishes, can't fail and doesn't change the store, and `e2'` doesn't use `x`
      if e1.pure && !mayFail H σ e1 && !(freeNames [] e2').contains x then e2'
      else .letin x e1' e2'
    | .binop op a b =>
      -- `a + 0`, `a - 0`, `a * 1`, `a / 1` become `a`, and `0 + b`, `1 * b` become `b`
      if rightIdentity H σ op a b then opt H σ a
      else if leftIdentity H σ op a b then opt H σ b
      else .binop op (opt H σ a) (opt H σ b)
    | .cons a b => .cons (opt H σ a) (opt H σ b)
    | .ite c t e =>
      match constOf H σ c with
      -- if the condition is certainly `true` only the `then` branch remains
      | some (.bool true) => opt H ((σ.assume c true).getD σ) t
      | some (.bool false) => opt H ((σ.assume c false).getD σ) e
      | _ =>
        -- each branch, knowing the condition (`σ` if the branch can't be taken)
        .ite (opt H σ c) (opt H ((σ.assume c true).getD σ) t)
          (opt H ((σ.assume c false).getD σ) e)
    | .matchList s n x xs c =>
      let vs := aeval H σ s
      .matchList (opt H σ s) (opt H σ n) x xs
        (opt H ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c)
    | .assert c =>
      match constOf H σ c with
      -- the assertion certainly holds
      | some (.bool true) => .unit
      | _ => .assert (opt H σ c)
    | .alloc site n v => .alloc site (opt H σ n) (opt H σ v)
    | .get a i => .get (opt H σ a) (opt H σ i)
    | .set a i v => .set (opt H σ a) (opt H σ i) (opt H σ v)
    | .len a => .len (opt H σ a)
    | .ref site v => .ref site (opt H σ v)
    | .deref r => .deref (opt H σ r)
    | .assign r v => .assign (opt H σ r) (opt H σ v)
    | .exn t v => .exn t (opt H σ v)
    | .raise v => .raise (opt H σ v)
    | .tryw a k h => .tryw (opt H σ a) k (opt H ((k, AVal.top) :: σ) h)
    | .exnCase s t x h m => .exnCase (opt H σ s) t x (opt H ((x, AVal.top) :: σ) h) (opt H σ m)
    | e => e

/-- A program optimised, with the hints inferred for it. `σ` describes its free
    variables. -/
def optimize (σ : AEnv A) (e : Expr) : Expr := opt (inferHints σ e) σ e

end Diva.Opt
