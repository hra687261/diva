import Diva.Prove
import Diva.AbsInt.Infer
import Diva.AbsInt.ItvDomain

/-!
# Inferring contracts from the analysis (untrusted)

`diva prove --infer` gives each top-level function without a contract the contract
that the analysis infers for it (`diva hints`):
- `requires`: the interval of each parameter, such as `acc >= 0`;
- `ensures`: the interval of the result, for a recursive function, such as
  `result >= 0`. The analysis infers the result only for recursive functions.

`diva prove` then proves these contracts like the ones that the user writes. Nothing
here is trusted: a wrong contract is a proof that fails.

The analysis keys its hints by the names that `resolve` gives (`acc#2`), and
`diva prove` uses the names of the source (`acc`). `topDecls` matches the two: the
top-level declarations are in the same order in both.
-/

namespace Diva.SpecOfHints

open AbsInt

/-- The terms that say that the integer `x` is in the interval `i`, such as
    `x >= 0`. `none` if `i` is empty. -/
def boundTerms (x : String) : Itv → Option (List Term)
  | .bot => none
  | .range lo hi =>
    let low := match lo with | .fin n => [Term.binop .ge (.var x) (.int n)] | _ => []
    let high := match hi with | .fin n => [Term.binop .le (.var x) (.int n)] | _ => []
    some (low ++ high)

/-- The terms that say that `x` is in `a`, if `a` contains only integers. `none` if
    `a` may also be another kind of value (a boolean, a list, ...), or nothing. -/
def intTerms (x : String) (a : Flat Itv) : Option (List Term) :=
  if a.tt || a.ff || a.unit || a.list || a.fn || a.loc || a.ctor then none
  else boundTerms x a.int

/-- The top-level declarations of the program `e` after `resolve`, in order. For a
    function: its name if it can call itself, and the names of its parameters. `none`
    for a declaration that isn't a function, and for `;; e`. -/
def topDecls : Expr → List (Option (Option String × List String))
  | .letrec f x b e₂ => some (some f, x :: (Prove.moreParams b).1) :: topDecls e₂
  | .letin _ (.lam x b) e₂ => some (none, x :: (Prove.moreParams b).1) :: topDecls e₂
  | .letin _ _ e₂ => none :: topDecls e₂
  | _ => []

/-- The contract that the hints `H` give to the declaration `b`. `f` and `xs` are the
    names of the recursive function and of the parameters after `resolve`. `none` if
    a parameter may be something other than an integer. -/
def contractOf (H : Hints Itv) (b : Binding) (f : Option String) (xs : List String) :
    Option Spec := do
  let (x, rest) ← match b with
    | .recFn _ x e => some (x, (Prove.moreParams e).1)
    | .val _ (.lam x e) => some (x, (Prove.moreParams e).1)
    | .val _ _ => none
  let params := x :: rest
  let requires ← (params.zip xs).mapM fun (p, p') => intTerms p (H.param p')
  let ensures := match f with
    | some f' => (intTerms "result" (H.result f')).getD []
    | none => []
  return { requires := requires.flatten, ensures }

/-- `items`, where each function without a contract gets a contract, and the names of
    these functions. The contract comes from abstract interpretation:
    the intervals that `inferHints` (`diva hints`) infers for the parameters and the
    result become `requires` and `ensures`. `depth` is that of `inferHints`. -/
def inferContracts (items : List Item) (depth : Nat := 5) : List Item × List String :=
  let e := (resolve [] (Item.toExpr items)).run' {}
  let H := inferHints ([] : AEnv Itv) e (depth := depth)
  let pairs := (items.zip (topDecls e)).map fun (i, d) =>
    match i, d with
    | .decl b none, some (f, xs) =>
      match contractOf H b f xs with
      | some sp => (Item.decl b (some sp), [b.name])
      | none => (i, [])
    | _, _ => (i, [])
  -- the items after the last declaration (`;; e` at the end) are kept as they are
  (pairs.map (·.1) ++ items.drop pairs.length, pairs.flatMap (·.2))

end Diva.SpecOfHints
