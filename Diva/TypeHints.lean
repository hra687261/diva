import Diva.AbsInt.Aeval
import Diva.Desugar

/-!
# Entry points (untrusted)

The check starts from the top-level code, which OCaml always runs. With `--entry f,g`,
`f` and `g` are also called after it (`withEntries`), with any arguments of their
parameters' OCaml types (`Ty`), which trusts the OCaml type checker.
-/

namespace Diva

/-- A type of OCaml, as the frontend gives it. -/
inductive Ty where
  | int
  /-- The integers from `lo` to `hi`: `char`, `Int32.t`, `Int64.t`. -/
  | range (lo hi : Int)
  | bool | unit | ctor | fn
  | list (t : Ty)
  /-- A ref, with the type of its contents. -/
  | ref (t : Ty)
  | tuple (ts : List Ty)
  /-- A variant type: its constructors, each with the type of its argument, if any. -/
  | variant (cs : List (String × Option Ty))
  /-- Any value: a type variable, or a type that DIVA doesn't describe. -/
  | any
  deriving Inhabited, Repr

/-- The type of a parameter: the span of its `fun`, its name in the source, and its
    type. For the first parameter of a `let rec`, the span of the body. -/
structure TypeHint where
  start : Nat
  stop : Nat
  name : String
  ty : Ty
  deriving Inhabited, Repr

namespace Ty

open AbsInt AbsDomain NumDomain

variable {A : Type} [NumDomain A]

/-- The values of the type `t`. -/
partial def flat [Inhabited A] : Ty → Flat A
  -- a ref given by other code: any value, because the analysis describes a ref by the
  -- place of the program that creates it (see `withEntries`)
  | .ref _ => Flat.top
  | .int => Flat.ofInt AbsDomain.top
  | .range lo hi => Flat.ofInt (AbsDomain.join (const lo) (const hi))
  | .bool => Flat.bools true true
  | .unit => Flat.unitV
  | .ctor => Flat.ctorV
  | .fn => Flat.fnV
  | .list t => { Flat.listV with elem := some t.flat }
  | .tuple ts =>
    let ws := ts.map flat
    let tag := s!"%{ts.length}"
    let elem := ws.foldl Flat.join Flat.bot
    let comps : Flat A := { Flat.listV with
      items := some ws
      elem := some elem
      len := const ws.length }
    { Flat.bot with ctors := [tag], args := [(tag, comps)] }
  | .variant cs =>
    { Flat.bot with
      ctors := cs.map (·.1)
      args := cs.map fun (c, t) => (c, (t.map flat).getD Flat.unitV) }
  | .any => Flat.top

end Ty

/-- `x` without the `#n` that `resolve` adds. -/
def sourceName (x : String) : String :=
  (x.splitOn "#").headD x

/-- The sub-expressions of `e`, in the order of the positions of `Loc`. -/
def Expr.kids : Expr → List Expr
  | .int _ | .bool _ | .unit | .var _ | .nil => []
  | .lam _ b | .assert b | .len b | .listLen b | .ref _ b | .deref b | .ctor _ b | .raise b =>
    [b]
  | .app a b | .letin _ a b | .letrec _ _ a b | .binop _ a b | .cons a b | .get a b
  | .assign a b | .alloc _ a b | .tryw a _ b => [a, b]
  | .ite a b c | .matchList a b _ _ c | .set a b c | .ctorCase a _ _ b c => [a, b, c]

/-- The types `ts` of the parameters of `e`, keyed by their names in `e` (after
    `resolve`). `l` has the positions of `e`. -/
partial def paramTypes (ts : List TypeHint) (e : Expr) (l : Loc) : List (String × Ty) :=
  let find (sp : Span) (x : String) : List (String × Ty) :=
    match ts.find? fun t => t.start == sp.start && t.stop == sp.stop && t.name == sourceName x with
    | some t => [(x, t.ty)]
    | none => []
  let here := match e with
    | .lam x _ => find l.span x
    | .letrec _ x _ _ => find (l.kid 0).span x
    | _ => []
  here ++ (e.kids.zipIdx.flatMap fun (k, i) => paramTypes ts k (l.kid i))

/-- The hints of the types `ts` for the parameters of `e` (see `paramTypes`). -/
def typeHints {A : Type} [AbsInt.NumDomain A] [Inhabited A] (ts : List TypeHint) (e : Expr)
    (l : Loc) : List (String × AbsInt.Flat A) :=
  (paramTypes ts e l).map fun (x, t) => (x, t.flat)

/-- The first allocation site that `e` doesn't use: after those of its refs and arrays. -/
partial def Expr.sitesEnd (e : Expr) : Nat :=
  let here := match e with
    | .ref s _ | .alloc s _ _ => s + 1
    | _ => 0
  e.kids.foldl (fun n k => max n k.sitesEnd) here

/-- The top-level functions of `e` (after `resolve`), with their parameters. `l` has the
    positions of `e`: the span of each function is that of its declaration. -/
def topFns : Expr → Loc → List (String × List String × Span)
  | .letrec f x b r, l => (f, x :: lamParams b, l.span) :: topFns r (l.kid 1)
  | .letin f a r, l =>
    (if lamParams a |>.isEmpty then [] else [(f, lamParams a, l.span)]) ++ topFns r (l.kid 1)
  | _, _ => []

/-- `e` with `let _ = c in` before its last expression, after its top-level code. `lc`
    has the positions of `c`, and `l` those of `e`. -/
def atEnd (c : Expr) (lc : Loc) : Expr → Loc → LExpr
  | .letrec f x b r, l =>
    let r' := atEnd c lc r (l.kid 1)
    ⟨.letrec f x b r'.expr, .node l.span [l.kid 0, r'.loc]⟩
  | .letin x a r, l =>
    let r' := atEnd c lc r (l.kid 1)
    ⟨.letin x a r'.expr, .node l.span [l.kid 0, r'.loc]⟩
  | r, l => ⟨.letin "_" c r, .node l.span [lc, l]⟩

/-- The argument for a parameter of type `t`: the free name `a`, with the values of `t`.
    For a ref, a new ref at the site `s` (and `s + 1`, ... for a ref of a ref) that holds
    the argument for the type of its contents: the analysis knows a ref by the site that
    creates it, and its contents by the hint of that site. Also gives the next free site. -/
def argOf {A : Type} [AbsInt.NumDomain A] [Inhabited A] (a : String) :
    Ty → Nat → Expr × Nat × AbsInt.Flat A
  | .ref t, s =>
    let (c, s', v) := argOf a t (s + 1)
    (.ref s c, s', v)
  | t, s => (.var a, s, t.flat)

/-- `e`, then a call of each function of `fs`, with free names as arguments. `σ` gives
    these names the values of the types `ts`. A parameter that is a ref gets a new ref
    (`argOf`). `l` has the positions of `e`. -/
def withEntries {A : Type} [AbsInt.NumDomain A] [Inhabited A] (fs : List String)
    (ts : List TypeHint) (e : Expr) (l : Loc) : Except String (LExpr × AbsInt.AEnv A) := do
  let T := paramTypes ts e l
  let fns := topFns e l
  let mut out : LExpr := ⟨e, l⟩
  let mut σ : AbsInt.AEnv A := []
  let mut site := e.sitesEnd
  for name in fs do
    -- the last declaration of `name`: the one that the end of the program sees
    let some (f, xs, _) := (fns.filter (sourceName ·.1 == name)).getLast?
      | throw s!"no top-level function `{name}`"
    let mut call := Expr.var f
    for (x, i) in xs.zipIdx do
      let a := s!"%{name}.{i}"
      let (arg, next, v) := argOf (A := A) a ((T.lookup x).getD .any) site
      site := next
      call := .app call arg
      σ := σ ++ [(a, AbsInt.AVal.ofFlat v)]
    out := atEnd call (.leaf Span.prelude) out.expr out.loc
  return (out, σ)

end Diva
