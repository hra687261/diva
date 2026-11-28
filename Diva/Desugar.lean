import Diva.Loc

/-!
# From the parsed items to one expression

`Item.toExpr` turns the top-level items of a program into one expression, for
`run`, `check` and `opt`. The `requires` of each contract become `assert`s at the
start of the function's body.
-/

namespace Diva

/-- `length l` as an expression: a recursive function that counts the elements of `l`. -/
def lengthExpr (l : Expr) : Expr :=
  .letrec "%length" "%l"
    (.matchList (.var "%l") (.int 0) "_" "%rest"
      (.binop .add (.int 1) (.app (.var "%length") (.var "%rest"))))
    (.app (.var "%length") l)

/-- `l` has at least `k` elements, as an expression: `k` nested `match`es. -/
def atLeast : Nat → Expr → Expr
  | 0, _ => .bool true
  | k + 1, l => .matchList l (.bool false) "_" "%rest" (atLeast k (.var "%rest"))

/-- `not e`, as the parser reads it. -/
def notExpr (e : Expr) : Expr := .ite e (.bool false) (.bool true)

/-- `length l op n`, with `n` a small integer (see `Term.toExpr`), as `match`es on `l`
    (`atLeast`) rather than a call of `lengthExpr`. The analysis follows `match`es
    exactly, but gives `lengthExpr`'s result for all the lists it is called on.

    TODO: the analysis knows the lengths of lists (`Flat.len`), but a call of `lengthExpr`
    gives the result of its summary, whatever the list. A `length` primitive in the core
    language would give `length l` from `Flat.len`, for any `n`, and `unroll` would go
    away. -/
def lengthCmp (op : BinOp) (l : Expr) (n : Nat) : Option Expr :=
  match op with
  | .ge => some (atLeast n l)
  | .gt => some (atLeast (n + 1) l)
  | .lt => some (notExpr (atLeast n l))
  | .le => some (notExpr (atLeast (n + 1) l))
  | .eq => some (.ite (atLeast n l) (notExpr (atLeast (n + 1) l)) (.bool false))
  | .ne => some (notExpr (.ite (atLeast n l) (notExpr (atLeast (n + 1) l)) (.bool false)))
  | _ => none

/-- `n op m` is `m (flipCmp op) n`. -/
def flipCmp : BinOp → BinOp
  | .le => .ge | .lt => .gt | .ge => .le | .gt => .lt | op => op

/-- The term `t` of a contract as an expression. `ren` renames the names of the
    contract's header to the parameters of the code. `a && b` is `if a then b else false`,
    as the parser reads `&&`, and `a || b` is `if a then true else b`. A comparison
    `length l op n` with `n` from `0` to `unroll` is written as `match`es (`lengthCmp`). -/
def Term.toExpr (unroll : Nat) (ren : List (String × String)) : Term → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .var x => .var ((ren.lookup x).getD x)
  | .binop op a b =>
    let small (n : Int) : Option Nat := if 0 ≤ n && n ≤ unroll then some n.toNat else none
    let unrolled := match a, b with
      | .length l, .int n => (small n).bind (lengthCmp op (l.toExpr unroll ren))
      | .int n, .length l => (small n).bind (lengthCmp (flipCmp op) (l.toExpr unroll ren))
      | _, _ => none
    unrolled.getD (.binop op (a.toExpr unroll ren) (b.toExpr unroll ren))
  | .and a b => .ite (a.toExpr unroll ren) (b.toExpr unroll ren) (.bool false)
  | .or a b => .ite (a.toExpr unroll ren) (.bool true) (b.toExpr unroll ren)
  | .not a => notExpr (a.toExpr unroll ren)
  | .length a => lengthExpr (a.toExpr unroll ren)

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
    breaks the precondition fails, as in Eiffel or SPARK. `ensures` isn't checked.
    `unroll` is that of `Term.toExpr`. -/
def Binding.withRequires (unroll : Nat) (b : Binding) : Option Spec → Binding
  | none => b
  | some sp =>
    let check (params : List String) (body : Expr) : Expr :=
      let ren := sp.params.zip params
      sp.requires.foldr (fun t e => .letin "_" (.assert (t.toExpr unroll ren)) e) body
    match b with
    | .val f e => .val f (insideLams (check (lamParams e)) e)
    | .recFn f x e => .recFn f x (insideLams (check (x :: lamParams e)) e)

/-- A program is nested `let`s ending in the value of its last item. The `requires` of
    the contracts are checked at run time (`Binding.withRequires`, with `unroll`). -/
def Item.toExpr (unroll : Nat) : List Item → Expr
  | [] => .unit
  | [.expr e] => e
  | .expr e :: r => .letin "_" e (Item.toExpr unroll r)
  | [.decl b sp] => (b.withRequires unroll sp).bind (.var b.name)
  | .decl b sp :: r => (b.withRequires unroll sp).bind (Item.toExpr unroll r)

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
