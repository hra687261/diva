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
  | .lam _ b | .assert b | .len b | .ref _ b | .deref b | .ctor _ b | .raise b => [b]
  | .app a b | .letin _ a b | .letrec _ _ a b | .binop _ a b | .cons a b | .get a b
  | .assign a b | .alloc _ a b | .tryw a _ b => [a, b]
  | .ite a b c | .matchList a b _ _ c | .set a b c | .ctorCase a _ _ b c => [a, b, c]

/-- The hints of the types `ts` for the parameters of `e`, keyed by their names in `e`
    (after `resolve`). `l` has the positions of `e`. -/
partial def typeHints {A : Type} [AbsInt.NumDomain A] [Inhabited A] (ts : List TypeHint) (e : Expr)
    (l : Loc) : List (String × AbsInt.Flat A) :=
  let find (sp : Span) (x : String) : List (String × AbsInt.Flat A) :=
    match ts.find? fun t => t.start == sp.start && t.stop == sp.stop && t.name == sourceName x with
    | some t => [(x, t.ty.flat)]
    | none => []
  let here := match e with
    | .lam x _ => find l.span x
    | .letrec _ x _ _ => find (l.kid 0).span x
    | _ => []
  here ++ (e.kids.zipIdx.flatMap fun (k, i) => typeHints ts k (l.kid i))

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

/-- `e`, then a call of each function of `fs`, with free names as arguments. `σ` gives
    these names the values of the types `ts`. `l` has the positions of `e`. -/
def withEntries {A : Type} [AbsInt.NumDomain A] [Inhabited A] (fs : List String)
    (ts : List TypeHint) (e : Expr) (l : Loc) : Except String (LExpr × AbsInt.AEnv A) := do
  let T : List (String × AbsInt.Flat A) := typeHints ts e l
  let fns := topFns e l
  let mut out : LExpr := ⟨e, l⟩
  let mut σ : AbsInt.AEnv A := []
  for name in fs do
    -- the last declaration of `name`: the one that the end of the program sees
    let some (f, xs, _) := (fns.filter (sourceName ·.1 == name)).getLast?
      | throw s!"no top-level function `{name}`"
    let args := xs.zipIdx.map fun (x, i) => (s!"%{name}.{i}", x)
    let call := args.foldl (fun c (a, _) => Expr.app c (.var a)) (.var f)
    out := atEnd call (.leaf Span.prelude) out.expr out.loc
    σ := σ ++ args.map fun (a, x) => (a, AbsInt.AVal.ofFlat ((T.lookup x).getD AbsInt.Flat.top))
  return (out, σ)

end Diva
