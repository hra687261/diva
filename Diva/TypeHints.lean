import Diva.AbsInt.AVal
import Diva.Loc

/-!
# Types as hints (untrusted)

The OCaml frontend gives the type of each parameter (`Ty`). The parameters of a function
that nothing calls get the hint of their type, rather than any value (`Infer.unreached`).
So `let neg b = not b` is analysed with `b` a boolean. This trusts the OCaml type checker.
The other parameters get their hints from the calls.

These hints change only `diva hints` and the reports: the body of a function that nothing
calls can't make the program fail (`mayFail`).
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
      empty := ws.isEmpty }
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

end Diva
