import Diva.AbsInt.Aeval

/-!
# Hint inference (untrusted)

Finds the hints that `aeval` checks: each parameter's precondition and each
recursive function's result. Nothing here is proved: `aeval` checks every hint, so a
wrong one only costs precision.

`claims H σ e` lists what each hint must cover, in one pass of the optimistic
analysis under `H`:
- `(x, a)`: an argument `a` passed to a function of parameter `x`;
- `($f, r)`: the result `r` of the body of `f`, assuming `H`'s claims.

`up` grows the hints from `⊥`, with widening, until they cover all their claims.
`down` then shrinks them back to their claims, as long as they still cover them,
which recovers some of what widening lost.

Hints are keyed by name. The parser gives every parameter and recursive function a
name of its own (`resolve`), so each gets its own hint.

For a call `f a`, `a` becomes a claim on the parameter of the function called, when
the code shows that function (`callee`). In `g b a`, `b` is a claim on `g`'s first
parameter and `a` on its second. Otherwise `a` is not recorded, and the checker
gives `top` for the call if `a` is not in the precondition.
-/

namespace Diva.AbsInt

open AbsDomain

variable {A : Type} [NumDomain A]

/-- Widening: integers are widened, the other components joined (they are finite). -/
def Flat.widen (a b : Flat A) : Flat A :=
  { a.join b with int := AbsDomain.widen a.int b.int }

/-- The parameters of the nested `fun`s at the start of `b`.
    For `fun y -> fun z -> e` it gives `[y, z]`. If `b` is not a `fun`, it gives `[]`. -/
def lamParams : Expr → List String
  | .lam y b => y :: lamParams b
  | _ => []

/-- Each variable bound to a function known from the code, with its parameters
    (`[]`: a variable bound to anything else, which hides an outer one). -/
abbrev Callees := List (String × List String)

/-- The parameters `f` has not received yet: for `let rec g x y = ...`, `g` gives
    `[x, y]` and `g b` gives `[y]`. `[]` if the code doesn't show which function `f`
    is (e.g. `f` is a parameter). -/
def callee (C : Callees) : Expr → List String
  | .lam x b => x :: lamParams b
  | .var f => (C.lookup f).getD []
  -- A call `f b`. The argument `b` goes to the first parameter in `callee C f`.
  -- The other parameters in that list still have no argument. `drop 1` keeps them.
  | .app f _ => (callee C f).drop 1
  | _ => []

/-- `lastRes` without checking the hints (`aevalM true`): the value of `e` for
    `fun y -> fun z -> e`. -/
def lastResOpt (H : Hints A) (σ : AEnv A) (b : Expr) : Flat A :=
  lastResOf b (aevalM true H σ b)

/-- What each hint must cover, in one pass over `e`. It goes where the optimistic
    analysis goes, with the same environments. -/
def claims (H : Hints A) (C : Callees) (σ : AEnv A) : Expr → List (String × Flat A)
  | .binop _ a b => claims H C σ a ++ claims H C σ b
  | .letin x e1 e2 =>
    claims H C σ e1 ++
      claims H ((x, callee C e1) :: C) ((x, aevalM true H σ e1) :: σ) e2
  | .lam x b => claims H ((x, []) :: C) ((x, AVal.ofFlat (H.param x)) :: σ) b
  | .app f a =>
    let arg := match callee C f with
      | x :: _ => [(x, (aevalM true H σ a).flat)]
      | [] => []
    arg ++ claims H C σ f ++ claims H C σ a
  | .letrec f x b e2 =>
    -- `fails` doesn't change values, which are all the inference looks at
    let S : Summary A := ⟨H.param x, restPres H b, H.result f, false⟩
    let σb := (x, AVal.ofFlat S.pre) :: (f, AVal.summary S) :: σ
    let Cb := (x, []) :: (f, x :: lamParams b) :: C
    ("$" ++ f, lastResOpt H σb b) :: claims H Cb σb b ++
      claims H ((f, x :: lamParams b) :: C) ((f, AVal.summary S) :: σ) e2
  | .ite c t e =>
    let ac := aevalM true H σ c
    claims H C σ c ++
      (if ac.tt then ((σ.assume c true).map (claims H C · t)).getD [] else []) ++
      (if ac.ff then ((σ.assume c false).map (claims H C · e)).getD [] else [])
  | _ => []

/-- The hint keys of `e`: its parameters, and `$f` for each recursive function `f`. -/
def hintKeys : Expr → List String
  | .lam x b => x :: hintKeys b
  | .letrec f x b e2 => x :: ("$" ++ f) :: hintKeys b ++ hintKeys e2
  | .app a b | .letin _ a b | .binop _ a b => hintKeys a ++ hintKeys b
  | .ite c t e => hintKeys c ++ hintKeys t ++ hintKeys e
  | _ => []

/-- For each key of `H`, the join of its claims. A parameter that no call reaches
    may be called from anywhere: `top`. A function's result that nothing claims
    (dead code) is `bot`. -/
def collect (H : Hints A) (σ : AEnv A) (e : Expr) : Hints A :=
  let cs := claims H [] σ e
  H.map fun (k, _) =>
    match cs.filter (·.1 == k) with
    | [] => (k, if k.startsWith "$" then Flat.bot else Flat.top)
    | ps => (k, ps.foldl (fun acc p => acc.join p.2) Flat.bot)

/-- `H` covers all its claims. -/
def covers (H : Hints A) (σ : AEnv A) (e : Expr) : Bool :=
  (collect H σ e).all fun (k, a) => a.leq ((H.lookup k).getD Flat.top)

/-- Grow `H`, with widening, until it covers its claims (or `n` rounds pass). -/
def up (σ : AEnv A) (e : Expr) : Nat → Hints A → Hints A
  | 0, H => H
  | n + 1, H =>
    if covers H σ e then H
    else up σ e n ((H.zip (collect H σ e)).map fun ((k, old), (_, now)) => (k, old.widen now))

/-- Shrink `H` to its claims, as long as they still cover theirs (`n` rounds). -/
def down (σ : AEnv A) (e : Expr) : Nat → Hints A → Hints A
  | 0, H => H
  | n + 1, H =>
    let H' := collect H σ e
    if covers H' σ e then down σ e n H' else H

/-- Hints for `e`, whose free variables `σ` describes. Hints that are `top` are left
    out: a missing hint means `top`. -/
def inferHints (σ : AEnv A) (e : Expr) (rounds : Nat := 10) : Hints A :=
  let H₀ := (hintKeys e).eraseDups.map (·, Flat.bot)
  let H := down σ e rounds (up σ e rounds H₀)
  H.filter fun (_, a) => !Flat.top.leq a

end Diva.AbsInt
