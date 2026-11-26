import Diva.AbsInt.Aeval

/-!
# Hint inference (untrusted)

Finds the hints that `aeval` checks: each parameter's precondition and each
recursive function's result. Nothing here is proved: `aeval` checks every hint, so a
wrong one only costs precision.

`claims H σ e` lists what each hint must cover, in one pass of the optimistic
analysis under `H`:
- `(x, a)`: an argument `a` passed to a function of parameter `x`;
- `($f, r)`: the result `r` of the body of `f`, assuming `H`'s claims;
- `(!s, v)`: a value `v` written to a ref or an array of the allocation site `s`, and
  `(!s.length, n)`: the length `n` of an array created at `s`;
- `(C, v)`: the argument `v` of a tagged value `C v`, an exception for example.

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
  lastResOf b (aevalM true true H σ b)

/-- What each hint must cover, in one pass over `e`. It goes where the optimistic
    analysis goes, with the same environments. -/
def claims (H : Hints A) (C : Callees) (σ : AEnv A) : Expr → List (String × Flat A)
  | .binop _ a b | .cons a b => claims H C σ a ++ claims H C σ b
  | .matchList s n x xs c =>
    let vs := aevalM true true H σ s
    claims H C σ s ++
      (if vs.mayBeNil then claims H C σ n else []) ++
      (if vs.heads.leq Flat.bot then []
       else claims H ((xs, []) :: (x, []) :: C)
         ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c)
  | .letin x e1 e2 =>
    claims H C σ e1 ++
      claims H ((x, callee C e1) :: C) ((x, aevalM true true H σ e1) :: σ) e2
  | .lam x b => claims H ((x, []) :: C) ((x, AVal.ofFlat (H.param x)) :: σ) b
  | .app f a =>
    let arg := match callee C f with
      | x :: _ => [(x, (aevalM true true H σ a).flat)]
      | [] => []
    arg ++ claims H C σ f ++ claims H C σ a
  | .letrec f x b e2 =>
    -- `f`'s summary, as the analysis gives it
    let S : Summary A := (aevalM true true H σ (.letrec f x b (.var f))).sum.getD
      ⟨H.param x, restPres H b, H.result f, false, Flat.exnV⟩
    let σb := (x, AVal.ofFlat S.pre) :: (f, AVal.summary S) :: σ
    let Cb := (x, []) :: (f, x :: lamParams b) :: C
    ("$" ++ f, lastResOpt H σb b) :: claims H Cb σb b ++
      claims H ((f, x :: lamParams b) :: C) ((f, AVal.summary S) :: σ) e2
  | .ite c t e =>
    let ac := aevalM true true H σ c
    claims H C σ c ++
      (if ac.tt then ((σ.assume c true).map (claims H C · t)).getD [] else []) ++
      (if ac.ff then ((σ.assume c false).map (claims H C · e)).getD [] else [])
  -- a value written to the store: a claim on the contents of each site written to
  | .ref site v => (s!"!{site}", (aevalM true true H σ v).flat) :: claims H C σ v
  | .alloc site n v =>
    (s!"!{site}", (aevalM true true H σ v).flat) ::
      (s!"!{site}.length", (aevalM true true H σ n).flat) :: claims H C σ n ++ claims H C σ v
  | .assign r v =>
    let av := (aevalM true true H σ v).flat
    ((aevalM true true H σ r).refs.map (s!"!{·}", av)) ++ claims H C σ r ++ claims H C σ v
  | .set a i v =>
    let av := (aevalM true true H σ v).flat
    ((aevalM true true H σ a).arrs.map (s!"!{·}", av)) ++ claims H C σ a ++ claims H C σ i ++
      claims H C σ v
  | .deref a | .len a | .assert a | .raise a => claims H C σ a
  | .get a i => claims H C σ a ++ claims H C σ i
  -- a tagged value: a claim on the arguments of its constructor
  | .exn c v => (c, (aevalM true true H σ v).flat) :: claims H C σ v
  | .tryw a k h =>
    let ea := raisesM true true H σ a
    claims H C σ a ++
      (if ea.leq Flat.bot then [] else claims H ((k, []) :: C) ((k, AVal.ofFlat ea) :: σ) h)
  | .exnCase s c x h m =>
    let vs := aevalM true true H σ s
    claims H C σ s ++
      (if vs.mayBeTag c then claims H ((x, []) :: C) (hitEnv H σ s vs c x) h else []) ++
      (if vs.mayBeOtherTag c then claims H C (σ.bind s (vs.withoutTag c)) m else [])
  | .int _ | .bool _ | .unit | .var _ | .nil => []

/-- The hint keys of `e`: its parameters, `$f` for each recursive function `f`, for
    each allocation site `s`, `!s` (the contents) and, for an array, `!s.length`, and
    each constructor `C` of a tagged value (its arguments). -/
def hintKeys : Expr → List String
  | .lam x b => x :: hintKeys b
  | .letrec f x b e2 => x :: ("$" ++ f) :: hintKeys b ++ hintKeys e2
  | .app a b | .letin _ a b | .binop _ a b | .cons a b => hintKeys a ++ hintKeys b
  | .ite c t e | .matchList c t _ _ e => hintKeys c ++ hintKeys t ++ hintKeys e
  | .ref site v => s!"!{site}" :: hintKeys v
  | .alloc site n v => s!"!{site}" :: s!"!{site}.length" :: hintKeys n ++ hintKeys v
  | .assign a b | .get a b => hintKeys a ++ hintKeys b
  | .set a i v => hintKeys a ++ hintKeys i ++ hintKeys v
  | .deref a | .len a | .assert a | .raise a => hintKeys a
  | .exn c v => c :: hintKeys v
  | .tryw a _ h => hintKeys a ++ hintKeys h
  | .exnCase s _ _ h m => hintKeys s ++ hintKeys h ++ hintKeys m
  | .int _ | .bool _ | .unit | .var _ | .nil => []

/-- For each key of `H`, the join of its claims. A parameter that no call reaches
    may be called from anywhere: `top`. A function's result that nothing claims
    (dead code) is `bot`. -/
def collect (H : Hints A) (σ : AEnv A) (e : Expr) : Hints A :=
  let cs := claims H [] σ e
  H.map fun (k, _) =>
    match cs.filter (·.1 == k) with
    | [] => (k, if k.startsWith "$" then Flat.bot else Flat.top)
    | ps => (k, ps.foldl (fun acc p => acc.join p.2) Flat.bot)

/-- `H`, with the hints of `fixed` replacing those of `H` for the same keys. For example,
    `pin [(x, a)] [(x, b), (y, c)] = [(x, a), (y, c)]`. The inference calls `pin` after
    each step, so the hints of `fixed` never change. The checker still checks them. -/
def pin (fixed H : Hints A) : Hints A :=
  H.map fun (k, a) => (k, (fixed.lookup k).getD a)

/-- `H` covers all its claims, except those on the keys of `fixed`. -/
def covers (fixed H : Hints A) (σ : AEnv A) (e : Expr) : Bool :=
  (collect H σ e).all fun (k, a) =>
    (fixed.lookup k).isSome || a.leq ((H.lookup k).getD Flat.top)

/-- Grow `H`, with widening, until it covers its claims (or `n` rounds pass). -/
def up (fixed : Hints A) (σ : AEnv A) (e : Expr) : Nat → Hints A → Hints A
  | 0, H => H
  | n + 1, H =>
    if covers fixed H σ e then H
    else
      let H' := (H.zip (collect H σ e)).map fun ((k, old), (_, now)) => (k, old.widen now)
      up fixed σ e n (pin fixed H')

/-- Shrink `H` to its claims, as long as they still cover theirs (`n` rounds). -/
def down (fixed : Hints A) (σ : AEnv A) (e : Expr) : Nat → Hints A → Hints A
  | 0, H => H
  | n + 1, H =>
    let H' := pin fixed (collect H σ e)
    if covers fixed H' σ e then down fixed σ e n H' else H

/-- The hints for the program `e`: the values of each parameter and of each function
    result. `σ` gives the values of the variables that `e` uses without defining them.
    The hints of `fixed` (given by the user or an LLM) are used unchanged. A hint that
    allows any value (`top`) is left out, because a missing hint means `top`. -/
def inferHints (σ : AEnv A) (e : Expr) (fixed : Hints A := []) (rounds : Nat := 10) :
    Hints A :=
  let H₀ := pin fixed ((hintKeys e).eraseDups.map (·, Flat.bot))
  let H := down fixed σ e rounds (up fixed σ e rounds H₀)
  H.filter fun (_, a) => !Flat.top.leq a

end Diva.AbsInt
