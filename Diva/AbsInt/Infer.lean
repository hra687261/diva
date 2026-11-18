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

For a call `f a`, the value of `a` becomes a claim on the parameter of the
function called. The inference finds that function by reading the code. It
finds it in two cases: `f` is a function written in place (`fun x -> ...`), or
`f` is defined by `let` or `let rec` as a function.
Otherwise, for example when `f` is a parameter or the result of another call,
the argument is not recorded. The checker then gives `top` for that call if the
argument is not in the precondition.
-/

namespace Diva.AbsInt

open AbsDomain

variable {A : Type} [NumDomain A]

/-- Widening: integers are widened, the other components joined (they are finite). -/
def Flat.widen (a b : Flat A) : Flat A :=
  { a.join b with int := AbsDomain.widen a.int b.int }

/-- Each variable bound to a function known from the code, with its parameter
    (`none`: a variable bound to anything else, which hides an outer one). -/
abbrev Callees := List (String × Option String)

/-- The parameter a call to `f` reaches, if `f` is known from the code. -/
def callee (C : Callees) : Expr → Option String
  | .lam x _ => some x
  | .var f => (C.lookup f).join
  | _ => none

/-- What each hint must cover, in one pass over `e`. It goes where the optimistic
    analysis goes, with the same environments. -/
def claims (H : Hints A) (C : Callees) (σ : AEnv A) : Expr → List (String × Flat A)
  | .binop _ a b => claims H C σ a ++ claims H C σ b
  | .letin x e1 e2 =>
    claims H C σ e1 ++
      claims H ((x, callee C e1) :: C) ((x, aevalM true H σ e1) :: σ) e2
  | .lam x b => claims H ((x, none) :: C) ((x, AVal.ofFlat (H.param x)) :: σ) b
  | .app f a =>
    let arg := match callee C f with
      | some x => [(x, (aevalM true H σ a).flat)]
      | none => []
    arg ++ claims H C σ f ++ claims H C σ a
  | .letrec f x b e2 =>
    -- `fails` doesn't change values, which are all the inference looks at
    let S : Summary A := ⟨H.param x, H.result f, false⟩
    let σb := (x, AVal.ofFlat S.pre) :: (f, AVal.summary S) :: σ
    let Cb := (x, none) :: (f, some x) :: C
    ("$" ++ f, (aevalM true H σb b).flat) :: claims H Cb σb b ++
      claims H ((f, some x) :: C) ((f, AVal.summary S) :: σ) e2
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
