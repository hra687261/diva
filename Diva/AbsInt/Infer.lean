import Diva.AbsInt.Aeval

/-!
# Hint inference (untrusted)

Finds the hints that `aeval` checks: each parameter's precondition and each
recursive function's result. Nothing here is proved: `aeval` checks every hint, so a
wrong one only costs precision.

`claims ext H σ e` lists what each hint must cover, in one pass of the optimistic
analysis under `H`. With `ext`, this analysis is the one of `aevalExt`, which also
analyses arrays, refs, exceptions and the elements of lists. Without `ext`, it is the
one of the checker `aeval`, so the hints are those that the checker can confirm: `cert`
and `opt` use them. The claims are:
- `(x, a)`: an argument `a` passed to a function of parameter `x`;
- `($f, r)`: the result `r` of the body of `f`, assuming `H`'s claims;
- `(!s, v)`: a value `v` written to a ref or an array of the allocation site `s`, and
  `(!s.length, n)`: the length `n` of an array created at `s`.

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
def lastResOpt (ext : Bool) (H : Hints A) (σ : AEnv A) (b : Expr) : Flat A :=
  lastResOf b (aevalM true ext H σ b)

/-- What each hint must cover, in one pass over `e`. It goes where the optimistic
    analysis goes, with the same environments. -/
def claims (ext : Bool) (H : Hints A) (C : Callees) (σ : AEnv A) : Expr → List (String × Flat A)
  | .binop _ a b | .cons a b => claims ext H C σ a ++ claims ext H C σ b
  | .matchList s n x xs c =>
    let vs := aevalM true ext H σ s
    claims ext H C σ s ++
      (if vs.mayBeNilI then claims ext H C σ n else []) ++
      (if vs.headsI.leq Flat.bot then []
       else claims ext H ((xs, []) :: (x, []) :: C)
         ((xs, vs.tailsI) :: (x, AVal.ofFlat vs.headsI) :: σ) c)
  | .letin x e1 e2 =>
    claims ext H C σ e1 ++
      claims ext H ((x, callee C e1) :: C) ((x, aevalM true ext H σ e1) :: σ) e2
  | .lam x b => claims ext H ((x, []) :: C) ((x, AVal.ofFlat (H.param x)) :: σ) b
  | .app f a =>
    let arg := match callee C f with
      | x :: _ => [(x, (aevalM true ext H σ a).flat)]
      | [] => []
    arg ++ claims ext H C σ f ++ claims ext H C σ a
  | .letrec f x b e2 =>
    -- `f`'s summary, as the analysis gives it
    let S : Summary A := (aevalM true ext H σ (.letrec f x b (.var f))).sum.getD
      ⟨H.param x, restPres H b, H.result f, false, Flat.ctorV⟩
    let σb := (x, AVal.ofFlat S.pre) :: (f, AVal.summary S) :: σ
    let Cb := (x, []) :: (f, x :: lamParams b) :: C
    ("$" ++ f, lastResOpt ext H σb b) :: claims ext H Cb σb b ++
      claims ext H ((f, x :: lamParams b) :: C) ((f, AVal.summary S) :: σ) e2
  | .ite c t e =>
    let ac := aevalM true ext H σ c
    claims ext H C σ c ++
      (if ac.tt then ((σ.assume c true).map (claims ext H C · t)).getD [] else []) ++
      (if ac.ff then ((σ.assume c false).map (claims ext H C · e)).getD [] else [])
  -- a value written to the store: a claim on the contents of each site written to
  | .ref site v => (s!"!{site}", (aevalM true ext H σ v).flat) :: claims ext H C σ v
  | .alloc site n v =>
    (s!"!{site}", (aevalM true ext H σ v).flat) ::
      (s!"!{site}.length", (aevalM true ext H σ n).flat) ::
        claims ext H C σ n ++ claims ext H C σ v
  | .assign r v =>
    let av := (aevalM true ext H σ v).flat
    ((aevalM true ext H σ r).refs.map (s!"!{·}", av)) ++ claims ext H C σ r ++ claims ext H C σ v
  | .set a i v =>
    let av := (aevalM true ext H σ v).flat
    ((aevalM true ext H σ a).arrs.map (s!"!{·}", av)) ++ claims ext H C σ a ++
      claims ext H C σ i ++ claims ext H C σ v
  | .deref a | .len a | .assert a | .raise a => claims ext H C σ a
  | .get a i => claims ext H C σ a ++ claims ext H C σ i
  -- `C v`: the claims of `v`
  | .ctor _ v => claims ext H C σ v
  | .tryw a k h =>
    let ea := raisesM true ext H σ a
    claims ext H C σ a ++
      (if ea.leq Flat.bot then [] else claims ext H ((k, []) :: C) ((k, AVal.ofFlat ea) :: σ) h)
  | .ctorCase s c x h m =>
    let vs := aevalM true ext H σ s
    claims ext H C σ s ++
      (if vs.mayBeCtor c then claims ext H ((x, []) :: C) (hitEnv σ s vs c x) h else []) ++
      (if vs.mayBeOtherCtor c then claims ext H C (σ.bind s (vs.withoutCtor c)) m else [])
  | .int _ | .bool _ | .unit | .var _ | .nil => []

/-- The hint keys of `e`: its parameters, `$f` for each recursive function `f`, for
    each allocation site `s`, `!s` (the contents) and, for an array, `!s.length`. -/
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
  | .ctor _ v => hintKeys v
  | .tryw a _ h => hintKeys a ++ hintKeys h
  | .ctorCase s _ _ h m => hintKeys s ++ hintKeys h ++ hintKeys m
  | .int _ | .bool _ | .unit | .var _ | .nil => []

/-- The hint of a key that no code claims anything on. A parameter that no call reaches
    may be called from anywhere: `top`, or a value of its type if `types` gives it
    (`TypeHints.lean`). A function's result that nothing claims (dead code) is `bot`. -/
def unclaimed (types : Hints A) (k : String) : Flat A :=
  if k.startsWith "$" then Flat.bot else (types.lookup k).getD Flat.top

/-- For each key of `H`, the join of its claims. A key without claims keeps its hint in
    `H` if `keep`, else it gets `unclaimed types`. -/
def collect (ext : Bool) (H : Hints A) (σ : AEnv A) (e : Expr) (keep : Bool := false)
    (types : Hints A := []) : Hints A :=
  let cs := claims ext H [] σ e
  H.map fun (k, old) =>
    match cs.filter (·.1 == k) with
    | [] => (k, if keep then old else unclaimed types k)
    | ps => (k, ps.foldl (fun acc p => acc.join p.2) Flat.bot)

/-- `H`, with the hints of `fixed` replacing those of `H` for the same keys. For example,
    `pin [(x, a)] [(x, b), (y, c)] = [(x, a), (y, c)]`. The inference calls `pin` after
    each step, so the hints of `fixed` never change. The checker still checks them. -/
def pin (fixed H : Hints A) : Hints A :=
  H.map fun (k, a) => (k, (fixed.lookup k).getD a)

/-- `H` covers all its claims, except those on the keys of `fixed`. With `keep`, a key
    without claims is covered. -/
def covers (ext : Bool) (fixed H : Hints A) (σ : AEnv A) (e : Expr) (keep : Bool := false)
    (types : Hints A := []) : Bool :=
  (collect ext H σ e keep types).all fun (k, a) =>
    (fixed.lookup k).isSome || a.leq ((H.lookup k).getD Flat.top)

/-- Grow `H` until it covers its claims (or `n` rounds pass): by joins in the first `delay`
    rounds, then with widening. The joins find the hints of claims that depend on each
    other, such as those of `x` and `y` for `f x = g (x + 1)` and `g y = f y`, before
    widening makes them `top`. The parts of the hints deeper than `depth` levels are
    forgotten, so that the hints stay finite.

    A key without claims keeps its hint: the code that would claim something on it may
    not be reached yet, because the hints of the code around it are still too small. For
    example, the parameter of a loop inside another loop gets claims only once the
    parameter of the outer loop has some values. -/
def up (ext : Bool) (fixed : Hints A) (σ : AEnv A) (e : Expr) (depth delay : Nat) : Nat → Hints A → Hints A
  | 0, H => H
  | n + 1, H =>
    if covers ext fixed H σ e (keep := true) then H
    else
      let H' := (H.zip (collect ext H σ e (keep := true))).map fun ((k, old), (_, now)) =>
        (k, (if delay > 0 then old.join now else old.widen now).trunc depth)
      up ext fixed σ e depth (delay - 1) n (pin fixed H')

/-- `H`, where each key without claims gets `unclaimed types`. After `up`, these keys are
    those of code that nothing reaches, such as the parameter of a function that nothing
    calls. -/
def unreached (ext : Bool) (types H : Hints A) (σ : AEnv A) (e : Expr) : Hints A :=
  let cs := claims ext H [] σ e
  H.map fun (k, a) => if cs.any (·.1 == k) then (k, a) else (k, unclaimed types k)

/-- Shrink `H` to its claims, as long as they still cover theirs (`n` rounds). -/
def down (ext : Bool) (types fixed : Hints A) (σ : AEnv A) (e : Expr) :
    Nat → Hints A → Hints A
  | 0, H => H
  | n + 1, H =>
    let H' := pin fixed (collect ext H σ e (types := types))
    if covers ext fixed H' σ e (types := types) then down ext types fixed σ e n H' else H

/-- The hints for the program `e`: the values of each parameter and of each function
    result. `σ` gives the values of the variables that `e` uses without defining them.
    The hints of `fixed` (given by the user or an LLM) are used unchanged. `types` gives
    the types of parameters, for those that no code reaches (`unclaimed`). A hint that
    allows any value (`top`) is left out, because a missing hint means `top`.
    The hints describe the parts of lists and other ADT values down to `depth`
    levels. -/
def inferHints (σ : AEnv A) (e : Expr) (fixed : Hints A := []) (rounds : Nat := 10)
    (ext : Bool := false) (types : Hints A := []) (depth : Nat := 5) : Hints A :=
  let H₀ := pin fixed ((hintKeys e).eraseDups.map (·, Flat.bot))
  -- `up` again: with `unclaimed` for the parameters of the functions that nothing calls, the
  -- code of these functions is reached, and its keys get claims
  let H₁ := up ext fixed σ e depth 3 rounds H₀
  let H₂ := up ext fixed σ e depth 3 rounds (pin fixed (unreached ext types H₁ σ e))
  let H := down ext types fixed σ e rounds H₂
  H.filter fun (_, a) => !Flat.top.leq a

end Diva.AbsInt
