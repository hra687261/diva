import Diva.Loc

/-!
# From the parsed items to one expression

`Item.toExpr` turns the top-level items of a program into one expression, for
`run`, `check` and `opt`. The `requires` of each contract become `assert`s at the
start of the function's body.
-/

namespace Diva

/-- The term `t` of a contract as an expression. `ren` renames the names of the
    contract's header to the parameters of the code. `a && b` is `if a then b else false`,
    as the parser reads `&&`. -/
def Term.toExpr (ren : List (String × String)) : Term → Expr
  | .int n => .int n
  | .var x => .var ((ren.lookup x).getD x)
  | .binop op a b => .binop op (a.toExpr ren) (b.toExpr ren)
  | .and a b => .ite (a.toExpr ren) (b.toExpr ren) (.bool false)

/-- `e` with `k` applied inside its leading `fun`s: `fun x -> fun y -> b` gives
    `fun x -> fun y -> k b`. -/
def insideLams (k : Expr → Expr) : Expr → Expr
  | .lam x b => .lam x (insideLams k b)
  | e => k e

/-- The parameters of the leading `fun`s of `e`. -/
def lamParams : Expr → List String
  | .lam x b => x :: lamParams b
  | _ => []

/-- The declaration `b`, where the `requires` of its contract `sp` are checked at the
    start of its body, once all its parameters are given: `requires t` becomes
    `assert t;`. So in the body, after the checks, the precondition holds. A call that
    breaks the precondition fails, as in Eiffel or SPARK. `ensures` isn't checked. -/
def Binding.withRequires (b : Binding) : Option Spec → Binding
  | none => b
  | some sp =>
    let check (params : List String) (body : Expr) : Expr :=
      let ren := sp.params.zip params
      sp.requires.foldr (fun t e => .letin "_" (.assert (t.toExpr ren)) e) body
    match b with
    | .val f e => .val f (insideLams (check (lamParams e)) e)
    | .recFn f x e => .recFn f x (insideLams (check (x :: lamParams e)) e)

/-- A program is nested `let`s ending in the value of its last item. The `requires` of
    the contracts are checked at run time (`Binding.withRequires`). -/
def Item.toExpr : List Item → Expr
  | [] => .unit
  | [.expr e] => e
  | .expr e :: r => .letin "_" e (Item.toExpr r)
  | [.decl b sp] => (b.withRequires sp).bind (.var b.name)
  | .decl b sp :: r => (b.withRequires sp).bind (Item.toExpr r)

/-- The positions of `insideLams k e`, from the positions `l` of `e`. `kl` gives the
    positions of `k b` from those of `b`. -/
def insideLamsLoc (kl : Loc → Loc) : Expr → Loc → Loc
  | .lam _ b, l => .node l.span [insideLamsLoc kl b (l.kid 0)]
  | _, l => kl l

/-- The positions of `b.withRequires sp`, from the positions `l` of the expression
    bound by `b`. The checks get an empty span at the start of the body: they are added
    there, and have no source text. -/
def Binding.withRequiresLoc (b : Binding) (l : Loc) : Option Spec → Loc
  | none => l
  | some sp =>
    let check (bl : Loc) : Loc :=
      let start : Span := ⟨bl.span.start, bl.span.start⟩
      sp.requires.foldr (fun _ r => .node bl.span [.node start [.leaf start], r]) bl
    match b with
    | .val _ e | .recFn _ _ e => insideLamsLoc check e l

/-- The positions of `Item.toExpr`, from the items and their positions. -/
def Item.toLoc : List (Item × Loc) → Loc
  | [] => default
  | [(.expr _, l)] => l
  | (.expr _, l) :: r => .node l.span [l, Item.toLoc r]
  | [(.decl b sp, l)] => .node l.span [b.withRequiresLoc l sp, .leaf l.span]
  | (.decl b sp, l) :: r => .node l.span [b.withRequiresLoc l sp, Item.toLoc r]

end Diva
