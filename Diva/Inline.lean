import Diva.Loc

/-!
# Copies of functions at their calls (untrusted)

A function has one summary for all its calls, so a call can be reported because of
another: in `let f x = if x < 0 then raise E else x in f 1; f (-1)`, `f 1` may raise `E`.

`expand` replaces a call `f a b` of `let f = fun x -> fun y -> e` by
`let x = a in let y = b in e`, which is analysed with the values of `a` and `b` only.
Only calls that give all the parameters of a non-recursive `f` are replaced. `f` is dropped
if all its calls are.

Only the analysis that isn't proved yet uses the copies (`Report.mayFailUnproved`). The
names must be unique (`resolve`), so that a copy hides no name at the call.

TODO: recursive functions, whose copies would potentially never end. Options, from
the simplest: unroll once (the recursive calls of the copy use the summary of `f`),
one summary per call site (k-CFA), or one summary per abstract argument, kept
finite by widening.
-/

namespace Diva.Inline

/-- A function whose calls can be replaced: its parameters, its body, and the positions of
    the body. -/
structure Def where
  params : List String
  body : Expr
  loc : Loc

/-- The parameters and the body of `e` if it is a `fun`, with the positions `l` of `e`. -/
def lamsOf : Expr → Loc → List String × Expr × Loc
  | .lam x b, l =>
    let (xs, body, lb) := lamsOf b (l.kid 0)
    (x :: xs, body, lb)
  | e, l => ([], e, l)

/-- The function called by `e` and the arguments, with their positions: `f a b` gives
    `f` and `[a, b]`. -/
def spine : Expr → Loc → Expr × List LExpr
  | .app f a, l =>
    let (g, args) := spine f (l.kid 0)
    (g, args ++ [⟨a, l.kid 1⟩])
  | e, _ => (e, [])

/-- The name that marks a copy: `let %call = () in ...`, with the span of the call, so
    that the messages about the copy can name the call (`Report.diagnose`). -/
def callMark : String := "%call"

/-- The copy of the body `d` of a call, with the arguments `args`:
    `let %call = () in let x = a in let y = b in body`. `sp` is the span of the call. -/
def copy (sp : Span) (d : Def) (args : List LExpr) : LExpr :=
  let e : LExpr := (d.params.zip args).foldr
    (fun ((x, a) : String × LExpr) (e : LExpr) => ⟨.letin x a.expr e.expr, .node sp [a.loc, e.loc]⟩)
    ⟨d.body, d.loc⟩
  ⟨.letin callMark .unit e.expr, .node sp [.leaf sp, e.loc]⟩

/-- `e` with its calls replaced by copies, where `D` gives the functions whose calls can
    be replaced. `l` has the positions of `e`. -/
partial def expand (D : List (String × Def)) : Expr → Loc → LExpr
  | .letin f a b, l =>
    let a := expand D a (l.kid 0)
    let (xs, body, lb) := lamsOf a.expr a.loc
    let D' := if xs.isEmpty then D.filter (·.1 != f)
      else (f, ⟨xs, body, lb⟩) :: D
    let b' := expand D' b (l.kid 1)
    -- `f` is dropped if it was called, and all its calls were replaced
    if !xs.isEmpty && (freeNames [] b).contains f && !(freeNames [] b'.expr).contains f then b'
    else ⟨.letin f a.expr b'.expr, .node l.span [a.loc, b'.loc]⟩
  | e@(.app f a), l =>
    -- a call with all the arguments of a function of `D` is replaced. Another call is
    -- kept: the calls in its parts may be replaced.
    let (g, args) := spine e l
    let full := match g with
      | .var g => (D.lookup g).filter fun (d : Def) => d.params.length == args.length
      | _ => none
    match full with
    | some d => copy l.span d (args.map fun (a : LExpr) => expand D a.expr a.loc)
    | none => two .app (expand D f (l.kid 0)) (expand D a (l.kid 1)) l
  | .lam x b, l => one (.lam x) (expand D b (l.kid 0)) l
  | .letrec f x b e, l => two (.letrec f x) (expand D b (l.kid 0)) (expand D e (l.kid 1)) l
  | .ite c t e, l =>
    three .ite (expand D c (l.kid 0)) (expand D t (l.kid 1)) (expand D e (l.kid 2)) l
  | .binop op a b, l => two (.binop op) (expand D a (l.kid 0)) (expand D b (l.kid 1)) l
  | .cons a b, l => two .cons (expand D a (l.kid 0)) (expand D b (l.kid 1)) l
  | .matchList s n x xs c, l =>
    three (fun s n c => .matchList s n x xs c) (expand D s (l.kid 0)) (expand D n (l.kid 1))
      (expand D c (l.kid 2)) l
  | .assert c, l => one .assert (expand D c (l.kid 0)) l
  | .alloc s n v, l => two (.alloc s) (expand D n (l.kid 0)) (expand D v (l.kid 1)) l
  | .get a i, l => two .get (expand D a (l.kid 0)) (expand D i (l.kid 1)) l
  | .set a i v, l =>
    three .set (expand D a (l.kid 0)) (expand D i (l.kid 1)) (expand D v (l.kid 2)) l
  | .len a, l => one .len (expand D a (l.kid 0)) l
  | .listLen a, l => one .listLen (expand D a (l.kid 0)) l
  | .ref s v, l => one (.ref s) (expand D v (l.kid 0)) l
  | .deref r, l => one .deref (expand D r (l.kid 0)) l
  | .assign r v, l => two .assign (expand D r (l.kid 0)) (expand D v (l.kid 1)) l
  | .ctor c v, l => one (.ctor c) (expand D v (l.kid 0)) l
  | .raise v, l => one .raise (expand D v (l.kid 0)) l
  | .tryw a k h, l => two (fun a h => .tryw a k h) (expand D a (l.kid 0)) (expand D h (l.kid 1)) l
  | .ctorCase s c x h m, l =>
    three (fun s h m => .ctorCase s c x h m) (expand D s (l.kid 0)) (expand D h (l.kid 1))
      (expand D m (l.kid 2)) l
  | e@(.int _), l | e@(.bool _), l | e@.unit, l | e@(.var _), l | e@.nil, l => ⟨e, l⟩
where
  one (k : Expr → Expr) (a : LExpr) (l : Loc) : LExpr := ⟨k a.expr, .node l.span [a.loc]⟩
  two (k : Expr → Expr → Expr) (a b : LExpr) (l : Loc) : LExpr :=
    ⟨k a.expr b.expr, .node l.span [a.loc, b.loc]⟩
  three (k : Expr → Expr → Expr → Expr) (a b c : LExpr) (l : Loc) : LExpr :=
    ⟨k a.expr b.expr c.expr, .node l.span [a.loc, b.loc, c.loc]⟩

end Diva.Inline
