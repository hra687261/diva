import Diva.AbsInt.AVal

/-!
# Abstract evaluation

`aeval H σ e` over-approximates the values `e` can evaluate to (`AVal`), in any
`NumDomain`. Integers and booleans are tracked by value, the other kinds only by
kind; what isn't analysed yet (the store, catching exceptions) gives `top`.

A comparison `l < r` (or `≤`, `>`, `≥`) in an `if` narrows the variables it
compares in each branch, and a branch that can't be taken is skipped. `l = r`
narrows only in the branch where it holds, and `l <> r` only in the branch where
it doesn't: there, both sides keep only the values they share. Only
variables and constants are looked at in the comparison: `x < 5` narrows `x`,
`x + 1 < 5` doesn't.

Functions are not iterated. The hints `H` claim each parameter's range `P` and each
recursive function's result `R`. `aeval` only checks these claims.
- `fun x -> b` gives `⟨P, [], R, fails⟩`: `b`'s result and failure, with `x ∈ P`.
- `fun x -> fun y -> b` gives `⟨P, [Q], R, fails⟩`, with `Q` for `y`.
- A call gives `R` if the argument is in `P`, else `⊤`. With more parameters, it
  gives `⟨Q, [], R, fails⟩`.
- `let rec f` keeps `R` only if the body stays in `R`, assuming `R` for the
  recursive calls.
A wrong claim gives `⊤`.

`mayFail H σ e` says whether `e` may end in an error. It is defined with `aevalM`,
because each needs the other: a `fun` needs to know whether its body may fail, and
`mayFail` needs the values of the parts of `e`. Its soundness is in
`MayFail.lean`.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

/-- `(may be true, may be false)` for `x = y`, where `a` describes `x` and `b`
    describes `y`. `=` compares integers, booleans and `()`. -/
def eqCmp [NumDomain A] (a b : AVal A) : Bool × Bool :=
  let i := cmpEq a.int b.int
  (i.1 || (a.tt && b.tt) || (a.ff && b.ff) || (a.unit && b.unit),
   i.2 || (a.tt && b.ff) || (a.ff && b.tt))

/-- The values that both `a` and `b` describe, if `x = y` holds. Then `x` and `y`
    are the same integer, boolean or `()`, so the other kinds are dropped. -/
def eqMeet [NumDomain A] (a b : AVal A) : AVal A :=
  AVal.ofFlat { (Flat.bot : Flat A) with
    int := meet a.int b.int, tt := a.tt && b.tt, ff := a.ff && b.ff,
    unit := a.unit && b.unit }

/-- Abstract environment: what is known about each variable. -/
abbrev AEnv (A : Type) := List (String × AVal A)

namespace AEnv

variable [NumDomain A]

/-- What `σ` knows about `x` (`top` if nothing). -/
def get (σ : AEnv A) (x : String) : AVal A := (σ.lookup x).getD AVal.top

/-- What `σ` knows about a variable or a constant (`top` for anything else). -/
def atom (σ : AEnv A) : Expr → AVal A
  | .var x => σ.get x
  | .int k => AVal.ofInt (const k)
  | _ => AVal.top

/-- Record `a` for `e` if `e` is a variable that `σ` knows. A variable `σ` doesn't
    know is left out, so that `σ` keeps the same variables. -/
def bind (σ : AEnv A) : Expr → AVal A → AEnv A
  | .var x, a => if (σ.lookup x).isSome then (x, a) :: σ else σ
  | _, _ => σ

/-- `σ` narrowed by `l < r`, or `none` if `l < r` can't hold. -/
def refineLt (σ : AEnv A) (l r : Expr) : Option (AEnv A) :=
  if (cmpLt (σ.atom l).int (σ.atom r).int).1 then
    let p := assumeLt (σ.atom l).int (σ.atom r).int
    some ((σ.bind r (AVal.ofInt p.2)).bind l (AVal.ofInt p.1))
  else none

/-- `σ` narrowed by `l ≤ r`, or `none` if `l ≤ r` can't hold. -/
def refineLe (σ : AEnv A) (l r : Expr) : Option (AEnv A) :=
  if (cmpLe (σ.atom l).int (σ.atom r).int).1 then
    let p := assumeLe (σ.atom l).int (σ.atom r).int
    some ((σ.bind r (AVal.ofInt p.2)).bind l (AVal.ofInt p.1))
  else none

/-- `σ` narrowed by `l = r`: both sides get the values they share. -/
def refineEq (σ : AEnv A) (l r : Expr) : Option (AEnv A) :=
  let m := eqMeet (σ.atom l) (σ.atom r)
  some ((σ.bind r m).bind l m)

/-- `σ` narrowed by `c` evaluating to `b`, or `none` if it can't. -/
def assume (σ : AEnv A) : Expr → Bool → Option (AEnv A)
  | .binop .eq l r, true  => σ.refineEq l r
  | .binop .ne l r, false => σ.refineEq l r
  | .binop .lt l r, true  => σ.refineLt l r
  | .binop .lt l r, false => σ.refineLe r l
  | .binop .le l r, true  => σ.refineLe l r
  | .binop .le l r, false => σ.refineLt r l
  | .binop .gt l r, true  => σ.refineLt r l
  | .binop .gt l r, false => σ.refineLe l r
  | .binop .ge l r, true  => σ.refineLe r l
  | .binop .ge l r, false => σ.refineLt l r
  | _, _ => some σ

end AEnv

/-- A comparison's result, from `(may be true, may be false)`. -/
def ofCmp [NumDomain A] (p : Bool × Bool) : AVal A := AVal.bools p.1 p.2

/-- A binary operator on abstract values. -/
def abinop [NumDomain A] : BinOp → AVal A → AVal A → AVal A
  | .add, a, b => AVal.ofInt (add a.int b.int)
  | .sub, a, b => AVal.ofInt (sub a.int b.int)
  | .mul, a, b => AVal.ofInt (mul a.int b.int)
  | .div, a, b => AVal.ofInt (div a.int b.int)
  | .mod, a, b => AVal.ofInt (mod a.int b.int)
  | .lt, a, b => ofCmp (cmpLt a.int b.int)
  | .le, a, b => ofCmp (cmpLe a.int b.int)
  | .gt, a, b => ofCmp (cmpLt b.int a.int)
  | .ge, a, b => ofCmp (cmpLe b.int a.int)
  | .eq, a, b => ofCmp (eqCmp a b)
  | .ne, a, b => ofCmp (eqCmp a b).swap

/-- The square of an integer that `a` describes. It is `≥ 0`, which `mul a a` alone
    doesn't say: for `a = [-1, 2]`, `mul a a` is `[-2, 4]`. `[0, +∞]` is what
    `assumeLe` keeps of `top` above `0`. -/
def sqInt [NumDomain A] (a : A) : A := meet (mul a a) (assumeLe (const 0) (top : A)).2

/-- A binary operator on the expressions `ea` and `eb`, whose values `a` and `b`
    describe. `x * x`, with the same name on both sides, is a square (`sqInt`). -/
def abinopE [NumDomain A] (op : BinOp) (ea eb : Expr) (a b : AVal A) : AVal A :=
  match op, ea, eb with
  | .mul, .var x, .var y => if x = y then AVal.ofInt (sqInt a.int) else abinop op a b
  | _, _, _ => abinop op a b

/-- Join the results of the branches that can be taken (`none`: dead branch). -/
def joinOpt [NumDomain A] : Option (AVal A) → Option (AVal A) → AVal A
  | some a, some b => a.join b
  | some a, none => a
  | none, some b => b
  | none, none => AVal.bot

/-- Claims the analysis checks rather than finds: the precondition of each
    parameter `x` (key `x`), and the result of each recursive function `f`
    (key `$f`). Missing claims are `top`. -/
abbrev Hints (A : Type) := List (String × Flat A)

def Hints.param [NumDomain A] (H : Hints A) (x : String) : Flat A :=
  (H.lookup x).getD Flat.top

def Hints.result [NumDomain A] (H : Hints A) (f : String) : Flat A :=
  (H.lookup ("$" ++ f)).getD Flat.top

/-- The value of a call of `af` on `aa`. `af`'s summary `S` says: for an argument
    in `S.pre`, the function returns a value in `S.res`, or, if it has more
    parameters (`S.rest`), a closure for them.

    Normally, the call uses `S` if two checks pass: `af` is certainly a function
    described by this summary, and `aa` is in `S.pre`. Otherwise it gives `top`.

    With `opt`, which only the inference uses, the checks are skipped. -/
def apply [NumDomain A] (opt : Bool) (af aa : AVal A) : AVal A :=
  match af.sum with
  | some S =>
    if opt || (!af.fn && aa.flat.leq S.pre) then
      match S.rest with
      | [] => AVal.ofFlat S.res
      -- a curried function: the closure for the next parameters
      | P :: Ps => AVal.summary ⟨P, Ps, S.res, S.fails⟩
    else AVal.top
  | none => AVal.top

/-- Whether `e` is a `fun`. -/
def _root_.Diva.Expr.isLam : Expr → Bool
  | .lam _ _ => true
  | _ => false

/-- The preconditions of the parameters of the `fun`s that `b` starts with: for
    `fun y -> fun z -> e`, those of `y` and `z`. -/
def restPres [NumDomain A] (H : Hints A) : Expr → List (Flat A)
  | .lam y b => H.param y :: restPres H b
  | _ => []

/-- The result of `b`'s last body, from `b`'s value `v`: the summary's result if `b`
    is a `fun`, else `v`. -/
def lastResOf [NumDomain A] (b : Expr) (v : AVal A) : Flat A :=
  if b.isLam then (v.sum.map Summary.res).getD Flat.top else v.flat

/-- Whether `b`'s last body may fail, from `b`'s value `v`: the summary's `fails` if
    `b` is a `fun`, else `bodyFails`. -/
def lastFailsOf [NumDomain A] (b : Expr) (v : AVal A) (bodyFails : Bool) : Bool :=
  if b.isLam then (v.sum.map Summary.fails).getD true else bodyFails

/-! ## Kinds of values, for errors -/

/-- Any integer, and nothing else. -/
def Flat.ints [NumDomain A] : Flat A := Flat.ofInt AbsDomain.top

/-- Any boolean, and nothing else. -/
def Flat.anyBool [NumDomain A] : Flat A := Flat.bools true true

/-- `a` describes only values that `k` describes. -/
def AVal.within [NumDomain A] (a : AVal A) (k : Flat A) : Bool := a.flat.leq k

/-- `op` may fail on values that `a` and `b` describe. -/
def opMayFail [NumDomain A] : BinOp → AVal A → AVal A → Bool
  | .add, a, b | .sub, a, b | .mul, a, b | .lt, a, b | .le, a, b | .gt, a, b
  | .ge, a, b => !(a.within Flat.ints && b.within Flat.ints)
  -- also when the divisor may be `0`
  | .div, a, b | .mod, a, b =>
    !(a.within Flat.ints && b.within Flat.ints) || (cmpEq b.int (const 0)).1
  -- `=` needs two integers or two booleans (or two `()`, not looked at here)
  | .eq, a, b | .ne, a, b =>
    !((a.within Flat.ints && b.within Flat.ints) ||
      (a.within Flat.anyBool && b.within Flat.anyBool))

/-- Whether a call of `af` on `aa` may fail. It can't if `af` is only closures
    described by its summary `S`, `aa` is in `S.pre`, and either the function has
    more parameters (the call only builds a closure) or `S` says that the body
    doesn't fail. -/
def callMayFail [NumDomain A] (af aa : AVal A) : Bool :=
  match af.sum with
  | some S =>
    !(af.toFlat.leq Flat.bot && af.elems.isNone && aa.flat.leq S.pre &&
      (!S.rest.isEmpty || !S.fails))
  | none => true

mutual

/-- The analysis, checking the claims of `H`. The checker is `aeval` (`opt = false`).

    With `opt`, a claim is used even if it fails its check: a call gives the
    summary's result even if the argument isn't in the precondition. This isn't
    sound. Only the inference uses it, because its first guesses are always wrong:
    with checking, they would give `top`, and the next guesses would be `top`. -/
def aevalM [NumDomain A] (opt : Bool) (H : Hints A) (σ : AEnv A) : Expr → AVal A
  | .int n => AVal.ofInt (const n)
  | .bool b => AVal.bools b !b
  | .unit => AVal.unitV
  | .nil => AVal.listOf Flat.bot
  | .cons a b => (aevalM opt H σ a).cons (aevalM opt H σ b)
  | .var x => σ.get x
  | .binop op a b => abinopE op a b (aevalM opt H σ a) (aevalM opt H σ b)
  | .letin x e1 e2 => aevalM opt H ((x, aevalM opt H σ e1) :: σ) e2
  | .lam x b =>
    -- the body, analysed with `x` in its precondition
    let P := H.param x
    let σb := (x, AVal.ofFlat P) :: σ
    match b with
    | .lam _ _ =>
      -- a curried function: `x`, then the parameters of the inner function
      match (aevalM opt H σb b).sum with
      | some T => AVal.summary ⟨P, T.pre :: T.rest, T.res, T.fails⟩
      | none => AVal.fnV   -- doesn't happen: a `fun` has a summary
    | _ => AVal.summary ⟨P, [], (aevalM opt H σb b).flat, mayFailM opt H σb b⟩
  | .app f a => apply opt (aevalM opt H σ f) (aevalM opt H σ a)
  | .letrec f x b e2 =>
    -- the claimed summary, checked against the body (which may call `f`)
    let P := H.param x
    let Ps := restPres H b
    let R := H.result f
    let env (F : Bool) := (x, AVal.ofFlat P) :: (f, AVal.summary ⟨P, Ps, R, F⟩) :: σ
    -- whether the last body may fail, assuming that the recursive calls don't
    let fails := lastFailsOf b (aevalM opt H (env false) b) (mayFailM opt H (env false) b)
    -- the last body's result, assuming the claimed summary for the recursive calls
    let res := lastResOf b (aevalM opt H (env fails) b)
    let S : Summary A := ⟨P, Ps, R, fails⟩
    aevalM opt H ((f, if opt || res.leq R then AVal.summary S else AVal.fnV) :: σ) e2
  | .ite c t e =>
    -- a branch is taken only if the condition may have that value
    joinOpt
      (if (aevalM opt H σ c).tt then (σ.assume c true).map (aevalM opt H · t) else none)
      (if (aevalM opt H σ c).ff then (σ.assume c false).map (aevalM opt H · e) else none)
  | .assert _ => AVal.unitV
  | .exn _ _ => AVal.exnV
  | .raise _ => AVal.bot   -- never gives a value
  | .matchList s n x xs c =>
    -- a branch is taken only if the list may be `[]`, or may have a first element
    let vs := aevalM opt H σ s
    joinOpt
      (if vs.mayBeNil then some (aevalM opt H σ n) else none)
      (if vs.heads.leq Flat.bot then none
       else some (aevalM opt H ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c))
  | _ => AVal.top

/-- Whether `e` may end in an error: division by zero, a failed `assert`, a type
    error (like `1 + true`), an unbound variable, or an exception. The checker is
    `mayFail` (`opt = false`). -/
def mayFailM [NumDomain A] (opt : Bool) (H : Hints A) (σ : AEnv A) : Expr → Bool
  | .int _ | .bool _ | .unit | .nil | .lam _ _ => false
  -- a variable `σ` knows is bound (see `AEnv.Bound`)
  | .var x => (σ.lookup x).isNone
  | .binop op a b =>
    mayFailM opt H σ a || mayFailM opt H σ b ||
      opMayFail op (aevalM opt H σ a) (aevalM opt H σ b)
  | .cons a b =>
    mayFailM opt H σ a || mayFailM opt H σ b || !(aevalM opt H σ b).within Flat.listV
  | .letin x e1 e2 =>
    mayFailM opt H σ e1 || mayFailM opt H ((x, aevalM opt H σ e1) :: σ) e2
  | .app f a =>
    mayFailM opt H σ f || mayFailM opt H σ a ||
      callMayFail (aevalM opt H σ f) (aevalM opt H σ a)
  | .letrec f x b e2 =>
    -- `f` as in `aevalM`
    let P := H.param x
    let Ps := restPres H b
    let R := H.result f
    let env (F : Bool) := (x, AVal.ofFlat P) :: (f, AVal.summary ⟨P, Ps, R, F⟩) :: σ
    let fails := lastFailsOf b (aevalM opt H (env false) b) (mayFailM opt H (env false) b)
    let res := lastResOf b (aevalM opt H (env fails) b)
    let S : Summary A := ⟨P, Ps, R, fails⟩
    mayFailM opt H ((f, if opt || res.leq R then AVal.summary S else AVal.fnV) :: σ) e2
  | .ite c t e =>
    -- a branch counts only if it can be taken
    let ac := aevalM opt H σ c
    mayFailM opt H σ c || !ac.within Flat.anyBool ||
      (ac.tt && ((σ.assume c true).map (mayFailM opt H · t)).getD false) ||
      (ac.ff && ((σ.assume c false).map (mayFailM opt H · e)).getD false)
  | .assert c =>
    let ac := aevalM opt H σ c
    mayFailM opt H σ c || !ac.within Flat.anyBool || ac.ff
  | .matchList s n x xs c =>
    -- a branch counts only if it can be taken (as in `aevalM`)
    let vs := aevalM opt H σ s
    mayFailM opt H σ s || !vs.within Flat.listV ||
      (vs.mayBeNil && mayFailM opt H σ n) ||
      (!vs.heads.leq Flat.bot &&
        mayFailM opt H ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c)
  | .exn _ e => mayFailM opt H σ e
  -- `raise`, `try`, lists, arrays and refs: not analysed yet
  | _ => true

end

/-- The checker. -/
abbrev aeval [NumDomain A] (H : Hints A) (σ : AEnv A) (e : Expr) : AVal A :=
  aevalM false H σ e

/-- The checker for errors. -/
abbrev mayFail [NumDomain A] (H : Hints A) (σ : AEnv A) (e : Expr) : Bool :=
  mayFailM false H σ e

/-! ## Concretisation -/

/-- Every variable that `σ` knows is bound in `ρ`. -/
def AEnv.Bound (σ : AEnv A) (ρ : Env) : Prop :=
  ∀ x, (σ.lookup x).isSome = true → (ρ.lookup x).isSome = true

/-- The abstract environment a closure's body is checked in, against the summary
    `S`: `x` in the precondition and, for a recursive function, `f` with `S`. -/
def bodyEnv [NumDomain A] (s : Option String) (x : String) (S : Summary A) (σ : AEnv A) :
    AEnv A :=
  match s with
  | none => (x, AVal.ofFlat S.pre) :: σ
  | some f => (x, AVal.ofFlat S.pre) :: (f, AVal.summary S) :: σ

/-- The checks of a closure's body `b`, analysed in `σ`, against the preconditions
    `Ps` of its other parameters, the result `R` and `F` (whether it may fail).

    `b` must start with one `fun` per precondition in `Ps`. Each parameter is
    analysed in its precondition. The last body's result must be in `R`, and if
    `F` is `false`, the last body must not fail. -/
def Checked [NumDomain A] (H : Hints A) :
    AEnv A → Expr → List (Flat A) → Flat A → Bool → Prop
  | σ, b, [], R, F => (aeval H σ b).flat.sub R ∧ (F = false → mayFail H σ b = false)
  | σ, .lam y b, P :: Ps, R, F => Checked H ((y, AVal.ofFlat P) :: σ) b Ps R F
  | _, _, _ :: _, _, _ => False

/-- Concretisation: the values `a` describes.

    A closure is described by `a`'s summary `S` if its body was checked against a
    summary `S₀` that promises at least as much, in an abstract environment `σ`
    describing the closure's own. This records the checks rather than stating `Sat`
    directly: soundness can then be proved by induction on the evaluation, and `Sat`
    follows (`letrec_sat`). -/
inductive AVal.mem {A : Type} [NumDomain A] : AVal A → Value → Prop where
  -- a value described by the flags and the integers of `a`
  | flat {a : AVal A} {v : Value} : a.toFlat.mem v → AVal.mem a v
  -- a closure described by the summary `a.sum`
  | sum {a : AVal A} {S S₀ : Summary A} {s : Option String} {x : String} {b : Expr}
      {ρ : Env} (H : Hints A) (σ : AEnv A) :
      a.sum = some S →
      -- `S₀` promises at least as much as `S`: it accepts at least the same
      -- arguments, returns at most the same values, and fails only if `S` may
      S.pre.sub S₀.pre → Flat.subs S.rest S₀.rest → S₀.res.sub S.res →
      (S.fails = false → S₀.fails = false) →
      -- `σ` describes `ρ`
      (∀ y w, ρ.lookup y = some w → AVal.mem (σ.get y) w) → σ.Bound ρ →
      -- the body was checked against `S₀`
      Checked H (bodyEnv s x S₀ σ) b S₀.rest S₀.res S₀.fails →
      AVal.mem a (.clos s x b ρ)
  -- a list whose elements are in `a.elems`, and that is `[]` only if `a.mayNil`
  | list {a : AVal A} {e : Flat A} {v : Value} :
      a.elems = some e → e.listMem v → (v = .nil → a.mayNil = true) → AVal.mem a v

namespace AVal

variable {A : Type} [NumDomain A]

theorem mem_ofFlat {f : Flat A} {v : Value} (h : f.mem v) : (ofFlat f).mem v := .flat h

theorem mem_top (v : Value) : (top : AVal A).mem v := .flat (Flat.mem_top v)

theorem mem_bool (b : Bool) : (bools b !b : AVal A).mem (.bool b) := by
  cases b <;> exact .flat rfl

theorem mem_bools {p : Bool × Bool} {P : Prop} [Decidable P]
    (h : (P → p.1 = true) ∧ (¬ P → p.2 = true)) :
    (bools p.1 p.2 : AVal A).mem (.bool (decide P)) := .flat (Flat.mem_bools h)

theorem mem_int {a : AVal A} {n : Int} (h : a.mem (.int n)) : γ a.int n := by
  cases h with
  | flat h => exact h
  | list _ hm _ => exact hm.elim   -- not a list

theorem mem_tt {a : AVal A} (h : a.mem (.bool true)) : a.tt = true := by
  cases h with
  | flat h => exact h
  | list _ hm _ => exact hm.elim   -- not a list

theorem mem_ff {a : AVal A} (h : a.mem (.bool false)) : a.ff = true := by
  cases h with
  | flat h => exact h
  | list _ hm _ => exact hm.elim   -- not a list

theorem mem_unit {a : AVal A} (h : a.mem .unit) : a.unit = true := by
  cases h with
  | flat h => exact h
  | list _ hm _ => exact hm.elim   -- not a list

theorem mem_flat {a : AVal A} {v : Value} (h : a.mem v) : a.flat.mem v := by
  cases h with
  | flat h =>
    -- the same values, and possibly more closures
    cases v
    case bool c => cases c <;> simp_all [Flat.mem, flat]
    all_goals simp_all [Flat.mem, flat]
  | sum _ _ hS =>
    -- a closure of the summary: now "any closure"
    simp [Flat.mem, flat, hS]
  | list hE hm _ =>
    -- a list of `a.elems`: now "any list"
    cases v
    case nil | cons => simp [Flat.mem, flat, hE]
    all_goals exact hm.elim

/-- A list described by `a.elems` is described by an `AVal` whose `elems` and
    `mayNil` are those of `join a b`. -/
theorem mem_elems_l {a b : AVal A} {t : Flat A} {s : Option (Summary A)} {e : Flat A}
    {v : Value} (he : a.elems = some e) (hm : e.listMem v) (hn : v = .nil → a.mayNil = true) :
    ({ toFlat := t, sum := s, elems := Option.merge Flat.join a.elems b.elems,
       mayNil := (a.elems.isSome && a.mayNil) || (b.elems.isSome && b.mayNil) } : AVal A).mem v := by
  rw [he]
  -- `[]` only if `a.mayNil`
  cases b.elems with
  | none => exact .list rfl hm (fun hv => by simp [hn hv])
  | some e' =>
    exact .list rfl (Flat.listMem_mono (fun w hw => Flat.mem_join_l hw) v hm)
      (fun hv => by simp [hn hv])

/-- A list described by `b.elems` is described by an `AVal` whose `elems` and
    `mayNil` are those of `join a b`. -/
theorem mem_elems_r {a b : AVal A} {t : Flat A} {s : Option (Summary A)} {e : Flat A}
    {v : Value} (he : b.elems = some e) (hm : e.listMem v) (hn : v = .nil → b.mayNil = true) :
    ({ toFlat := t, sum := s, elems := Option.merge Flat.join a.elems b.elems,
       mayNil := (a.elems.isSome && a.mayNil) || (b.elems.isSome && b.mayNil) } : AVal A).mem v := by
  rw [he]
  -- `[]` only if `b.mayNil`
  cases a.elems with
  | none => exact .list rfl hm (fun hv => by simp [hn hv])
  | some e' =>
    exact .list rfl (Flat.listMem_mono (fun w hw => Flat.mem_join_r hw) v hm)
      (fun hv => by simp [hn hv])

theorem mem_join_l {a b : AVal A} {v : Value} (h : a.mem v) : (a.join b).mem v := by
  dsimp only [join, join.joinSum]
  split
  next S T hS hT =>
    split
    next hpre =>
      cases h with
      | flat h => exact .flat (Flat.mem_join_l h)
      | list hE hm hn => exact mem_elems_l hE hm hn
      | sum H σ hS' hP hPs hR hF hd hB hchk =>
        -- The closure is described by `a`'s summary `S`. We show that it is also
        -- described by the joined summary
        -- `⟨S.pre, S.rest, S.res ⊔ T.res, S.fails || T.fails⟩`.
        rw [hS] at hS'
        cases hS'
        -- Same preconditions. A result in `S.res` is also in `S.res ⊔ T.res`.
        refine .sum H σ rfl hP hPs (fun w hw => Flat.mem_join_l (hR w hw)) ?_ hd hB hchk
        -- If `S.fails || T.fails` is `false`, then `S.fails` is `false`.
        intro h
        simp only [Bool.or_eq_false_iff] at h
        exact hF h.1
    next => exact .flat (Flat.mem_join_l (mem_flat h))
  next S hS hT =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_l h)
    | list hE hm hn => exact mem_elems_l hE hm hn
    | sum H σ hS' hP hPs hR hF hd hB hchk =>
      -- the summary is kept
      rw [hS] at hS'
      exact .sum H σ hS' hP hPs hR hF hd hB hchk
  next _ _ hS =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_l h)
    | list hE hm hn => exact mem_elems_l hE hm hn
    | sum _ _ hS' =>
      -- `a` has no summary
      rw [hS] at hS'
      cases hS'

theorem mem_join_r {a b : AVal A} {v : Value} (h : b.mem v) : (a.join b).mem v := by
  dsimp only [join, join.joinSum]
  split
  next S T hS hT =>
    split
    next hpre =>
      simp only [Bool.and_eq_true] at hpre
      cases h with
      | flat h => exact .flat (Flat.mem_join_r h)
      | list hE hm hn => exact mem_elems_r hE hm hn
      | sum H σ hT' hP hPs hR hF hd hB hchk =>
        -- The closure is described by `b`'s summary `T`. We show that it is also
        -- described by the joined summary
        -- `⟨S.pre, S.rest, S.res ⊔ T.res, S.fails || T.fails⟩`.
        rw [hT] at hT'
        cases hT'
        -- `S`'s preconditions are equal to `T`'s (checked by `join`). A result in
        -- `T.res` is also in `S.res ⊔ T.res`.
        have hP' : S.pre.sub _ := fun w hw => hP w (Flat.mem_leq hw hpre.1.1.1)
        have hPs' := Flat.subs_of_leqs _ _ _ hpre.1.2 hPs
        refine .sum H σ rfl hP' hPs' (fun w hw => Flat.mem_join_r (hR w hw)) ?_ hd hB hchk
        -- If `S.fails || T.fails` is `false`, then `T.fails` is `false`.
        intro h
        simp only [Bool.or_eq_false_iff] at h
        exact hF h.2
    next => exact .flat (Flat.mem_join_r (mem_flat h))
  next S hS hT =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_r h)
    | list hE hm hn => exact mem_elems_r hE hm hn
    | sum _ _ hT' =>
      -- `b` has no summary
      rw [hT] at hT'
      cases hT'
  next =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_r h)
    | list hE hm hn => exact mem_elems_r hE hm hn
    | sum H σ hT' hP hPs hR hF hd hB hchk =>
      -- the summary is kept
      exact .sum H σ hT' hP hPs hR hF hd hB hchk

/-! ### Lists -/

/-- `cons` describes `vh :: vt`. -/
theorem mem_cons {h t : AVal A} {vh vt : Value} (hh : h.mem vh) (ht : t.mem vt)
    (hl : vt.isList = true) : (h.cons t).mem (.cons vh vt) := by
  unfold cons
  split
  case isTrue =>
    exact .flat rfl
  case isFalse hnl =>
    cases ht
    case flat ht =>
      -- `vt` is a list, so `t` may be any list: excluded by the `if`
      cases vt
      case nil | cons => exact absurd ht hnl
      all_goals simp [Value.isList] at hl
    case sum =>
      -- `vt` is a closure, not a list
      simp [Value.isList] at hl
    case list hE hm hn =>
      -- the elements of `t`, joined with `h`
      rw [hE]
      refine AVal.mem.list rfl ?_ ?_
      · -- `listMem` of `vh :: vt`: `vh` and the elements of `vt` are in the join
        unfold Flat.listMem
        constructor
        · -- `vh` is in `h`, so in the join
          exact Flat.mem_join_r (mem_flat hh)
        · -- the elements of `vt` are in `e`, so in the join
          exact Flat.listMem_mono (fun w hw => Flat.mem_join_l hw) vt hm
      · -- `vh :: vt` is not `[]`
        intro hv
        cases hv

/-- `heads` describes the first element of a list. -/
theorem mem_heads {a : AVal A} {vh vt : Value} (h : a.mem (.cons vh vt)) :
    a.heads.mem vh := by
  unfold heads
  split
  case isTrue => exact Flat.mem_top vh
  case isFalse hnl =>
    cases h
    case flat h => exact absurd h hnl   -- `a` may be any list: excluded by the `if`
    case list hE hm hn =>
      -- the elements of `a`
      rw [hE]
      exact hm.1

/-- `tails` describes the tail of a list. -/
theorem mem_tails {a : AVal A} {vh vt : Value} (h : a.mem (.cons vh vt)) :
    a.tails.mem vt := by
  unfold tails
  split
  case isTrue => exact mem_top vt
  case isFalse hnl =>
    cases h
    case flat h => exact absurd h hnl   -- `a` may be any list: excluded by the `if`
    case list hE hm hn =>
      -- a list of the elements of `a`
      rw [hE]
      exact .list rfl hm.2 (fun _ => rfl)

/-- If `a` describes `[]`, `a` may be `[]`. -/
theorem mayBeNil_of_mem {a : AVal A} (h : a.mem .nil) : a.mayBeNil = true := by
  cases h
  case flat h =>
    -- `a` may be any list
    have hl : a.list = true := h
    simp [mayBeNil, hl]
  case list hE _ hn => simp [mayBeNil, hE, hn rfl]

/-- If `a` describes a list `vh :: vt`, the first elements of `a` are not `⊥`. -/
theorem heads_not_bot {a : AVal A} {vh vt : Value} (h : a.mem (.cons vh vt)) :
    a.heads.leq Flat.bot = false := by
  cases hb : a.heads.leq Flat.bot
  case false => rfl
  case true => exact absurd (Flat.mem_leq (mem_heads h) hb) Flat.not_mem_bot

end AVal

/-! ## Soundness -/

/-- `σ` describes the values of `ρ`. -/
def AEnv.Describes [NumDomain A] (σ : AEnv A) (ρ : Env) : Prop :=
  ∀ x v, ρ.lookup x = some v → (σ.get x).mem v

namespace AEnv

variable [NumDomain A] {σ : AEnv A} {ρ : Env}

/-- If `σ` describes `ρ`, adding `x ↦ a` to `σ` and `x ↦ v` to `ρ` keeps it so,
    provided `a` describes `v`. -/
theorem Describes.cons {x : String} {a : AVal A} {v : Value} (hσ : σ.Describes ρ)
    (hv : a.mem v) : AEnv.Describes ((x, a) :: σ) ((x, v) :: ρ) := by
  unfold AEnv.Describes
  intro y w hy
  by_cases hxy : x = y
  · subst hxy
    simp [List.lookup] at hy
    subst hy
    simpa [get, List.lookup] using hv
  · have hyx : (y == x) = false := by simp; exact Ne.symm hxy
    simp [List.lookup, hyx] at hy
    simpa [get, List.lookup, hyx] using hσ y w hy

omit [NumDomain A] in
theorem Bound.cons {x : String} {a : AVal A} {v : Value} (hb : σ.Bound ρ) :
    AEnv.Bound ((x, a) :: σ) ((x, v) :: ρ) := by
  intro y hy
  by_cases hxy : y = x
  · subst hxy
    simp [List.lookup]
  · have hne : (y == x) = false := by simpa using hxy
    simp only [List.lookup, hne] at hy ⊢
    exact hb y hy

omit [NumDomain A] in
/-- A variable that isn't bound is unknown to `σ`. -/
theorem Bound.none {x : String} (hb : σ.Bound ρ) (hx : ρ.lookup x = none) :
    (σ.lookup x).isNone = true := by
  cases hs : σ.lookup x
  · rfl
  · have h := hb x (by simp [hs])
    simp [hx] at h

/-- A closure's body is checked in an abstract environment that knows only
    variables bound in its call environment. -/
theorem Bound.body {s : Option String} {x : String} {b : Expr} {S : Summary A}
    {va : Value} (hb : σ.Bound ρ) : (bodyEnv s x S σ).Bound (callEnv s x b ρ va) := by
  cases s
  case none => exact hb.cons
  case some f => exact hb.cons.cons

/-- A closure's body is checked in an abstract environment that describes its call
    environment, if the argument meets the precondition. -/
theorem Describes.body {H : Hints A} {s : Option String} {x : String} {b : Expr}
    {S : Summary A} {va : Value} (hσ : σ.Describes ρ) (hB : σ.Bound ρ)
    (hchk : Checked H (bodyEnv s x S σ) b S.rest S.res S.fails) (hv : S.pre.mem va) :
    (bodyEnv s x S σ).Describes (callEnv s x b ρ va) := by
  cases s
  case none => exact hσ.cons (.flat hv)
  case some f =>
    -- `f` is the closure itself, described by its summary by the same checks
    have hf : (AVal.summary S).mem (.clos (some f) x b ρ) :=
      .sum H σ rfl (Flat.sub_refl _) (Flat.subs_refl _) (Flat.sub_refl _) id hσ hB hchk
    exact (hσ.cons hf).cons (.flat hv)

omit [NumDomain A] in
theorem bind_bound {e : Expr} {a : AVal A} (hb : σ.Bound ρ) : (σ.bind e a).Bound ρ := by
  cases e
  case var x =>
    by_cases hk : (σ.lookup x).isSome
    · -- `x` was already known
      simp only [bind, hk, ↓reduceIte]
      intro y hy
      by_cases hxy : y = x
      · subst hxy
        exact hb y hk
      · have hne : (y == x) = false := by simpa using hxy
        simp only [List.lookup, hne] at hy
        exact hb y hy
    · simp only [bind, hk]
      exact hb
  all_goals exact hb

theorem refineLt_bound {σ' : AEnv A} {l r : Expr} (hb : σ.Bound ρ)
    (h : σ.refineLt l r = some σ') : σ'.Bound ρ := by
  unfold refineLt at h
  split at h
  · cases h
    exact bind_bound (bind_bound hb)
  · cases h

theorem refineLe_bound {σ' : AEnv A} {l r : Expr} (hb : σ.Bound ρ)
    (h : σ.refineLe l r = some σ') : σ'.Bound ρ := by
  unfold refineLe at h
  split at h
  · cases h
    exact bind_bound (bind_bound hb)
  · cases h

theorem refineEq_bound {σ' : AEnv A} {l r : Expr} (hb : σ.Bound ρ)
    (h : σ.refineEq l r = some σ') : σ'.Bound ρ := by
  unfold refineEq at h
  cases h
  exact bind_bound (bind_bound hb)

/-- Narrowing doesn't add variables. -/
theorem assume_bound {σ' : AEnv A} {c : Expr} {b : Bool} (hb : σ.Bound ρ)
    (h : σ.assume c b = some σ') : σ'.Bound ρ := by
  cases c
  case binop op l r =>
    cases op <;> cases b <;> simp only [assume] at h
    case lt.true  => exact refineLt_bound hb h
    case lt.false => exact refineLe_bound hb h
    case le.true  => exact refineLe_bound hb h
    case le.false => exact refineLt_bound hb h
    case gt.true  => exact refineLt_bound hb h
    case gt.false => exact refineLe_bound hb h
    case ge.true  => exact refineLe_bound hb h
    case ge.false => exact refineLt_bound hb h
    case eq.true  => exact refineEq_bound hb h
    case ne.false => exact refineEq_bound hb h
    -- the other conditions don't narrow
    all_goals
      cases h
      exact hb
  all_goals
    simp only [assume] at h
    cases h
    exact hb

theorem atom_sound {e : Expr} {μ μ' : Store} {v : Value} (hσ : σ.Describes ρ)
    (h : Eval ρ μ e (.ok v) μ') : (σ.atom e).mem v := by
  cases e
  case var x => cases h with | var hx => exact hσ x v hx
  case int => cases h; exact .flat (const_sound _)
  all_goals exact AVal.mem_top _

/-- Recording `a` for `e` keeps the description, if `a` describes `e`'s value. -/
theorem bind_sound {e : Expr} {a : AVal A} {μ μ' : Store} {v : Value} (hσ : σ.Describes ρ)
    (h : Eval ρ μ e (.ok v) μ') (ha : a.mem v) : (σ.bind e a).Describes ρ := by
  cases e
  case var x =>
    cases h with
    | var hx =>
      by_cases hk : (σ.lookup x).isSome
      · -- `x` is recorded with `a`
        simp only [bind, hk, ↓reduceIte]
        intro y w hy
        by_cases hxy : x = y
        · subst hxy
          rw [hx] at hy; cases hy
          simpa [get, List.lookup] using ha
        · have hyx : (y == x) = false := by simp; exact Ne.symm hxy
          simpa [get, List.lookup, hyx] using hσ y w hy
      · -- `σ` doesn't know `x`: nothing changes
        simp only [bind, hk]
        exact hσ
  all_goals exact hσ

/-- If `x = y` holds, `x` and `y` are the same value, and `eqMeet` describes it. -/
theorem eqMeet_sound {a b : AVal A} {va vb : Value} (ha : a.mem va) (hb : b.mem vb)
    (h : BinOp.eq.denote va vb = .ok (.bool true)) : va = vb ∧ (eqMeet a b).mem va := by
  cases va <;> cases vb <;> simp only [BinOp.denote] at h
  case int.int x y =>
    have hxy : x = y := by simpa using h
    subst hxy
    exact ⟨rfl, .flat (meet_sound (AVal.mem_int ha) (AVal.mem_int hb))⟩
  case bool.bool x y =>
    have hxy : x = y := by simpa using h
    subst hxy
    cases x
    · exact ⟨rfl, .flat (by simp [eqMeet, AVal.ofFlat, Flat.mem, AVal.mem_ff ha, AVal.mem_ff hb])⟩
    · exact ⟨rfl, .flat (by simp [eqMeet, AVal.ofFlat, Flat.mem, AVal.mem_tt ha, AVal.mem_tt hb])⟩
  case unit.unit =>
    exact ⟨rfl, .flat (by simp [eqMeet, AVal.ofFlat, Flat.mem, AVal.mem_unit ha, AVal.mem_unit hb])⟩
  all_goals cases h

theorem refineEq_sound {l r : Expr} {μ₁ μ₂ μ₃ μ₄ : Store} {va vb : Value}
    (hσ : σ.Describes ρ) (hl : Eval ρ μ₁ l (.ok va) μ₂) (hr : Eval ρ μ₃ r (.ok vb) μ₄)
    (h : BinOp.eq.denote va vb = .ok (.bool true)) :
    ∃ σ', σ.refineEq l r = some σ' ∧ σ'.Describes ρ := by
  -- both sides are the same value, which `eqMeet` describes
  obtain ⟨rfl, hm⟩ := eqMeet_sound (atom_sound hσ hl) (atom_sound hσ hr) h
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr hm) hl hm⟩

theorem refineLt_sound {l r : Expr} {μ₁ μ₂ μ₃ μ₄ : Store} {n m : Int}
    (hσ : σ.Describes ρ) (hl : Eval ρ μ₁ l (.ok (.int n)) μ₂)
    (hr : Eval ρ μ₃ r (.ok (.int m)) μ₄) (h : n < m) :
    ∃ σ', σ.refineLt l r = some σ' ∧ σ'.Describes ρ := by
  have ha : γ (σ.atom l).int n := AVal.mem_int (atom_sound hσ hl)
  have hb : γ (σ.atom r).int m := AVal.mem_int (atom_sound hσ hr)
  -- `l < r` is possible, so `refineLt` narrows instead of giving `none`
  have hmay := (cmpLt_sound ha hb).1 h
  unfold refineLt
  rw [ite_eq_left hmay]
  -- the narrowed values still describe `l` and `r`
  have hp := assumeLt_sound ha hb h
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr (.flat hp.2)) hl (.flat hp.1)⟩

theorem refineLe_sound {l r : Expr} {μ₁ μ₂ μ₃ μ₄ : Store} {n m : Int}
    (hσ : σ.Describes ρ) (hl : Eval ρ μ₁ l (.ok (.int n)) μ₂)
    (hr : Eval ρ μ₃ r (.ok (.int m)) μ₄) (h : n ≤ m) :
    ∃ σ', σ.refineLe l r = some σ' ∧ σ'.Describes ρ := by
  have ha : γ (σ.atom l).int n := AVal.mem_int (atom_sound hσ hl)
  have hb : γ (σ.atom r).int m := AVal.mem_int (atom_sound hσ hr)
  -- `l ≤ r` is possible, so `refineLe` narrows instead of giving `none`
  have hmay := (cmpLe_sound ha hb).1 h
  unfold refineLe
  rw [ite_eq_left hmay]
  -- the narrowed values still describe `l` and `r`
  have hp := assumeLe_sound ha hb h
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr (.flat hp.2)) hl (.flat hp.1)⟩

end AEnv

/-- Every operator but `=` and `<>` needs two integers. -/
theorem denote_ints {op : BinOp} {va vb v : Value} (hop : op ≠ .eq ∧ op ≠ .ne)
    (h : op.denote va vb = .ok v) : ∃ x y, va = .int x ∧ vb = .int y := by
  cases va <;> cases vb
  case int.int x y => exact ⟨x, y, rfl, rfl⟩
  all_goals cases op <;> simp_all [BinOp.denote]

/-- `=` gives a boolean. -/
theorem denote_eq_bool {va vb v : Value} (h : BinOp.eq.denote va vb = .ok v) :
    ∃ r, v = .bool r := by
  cases va <;> cases vb <;> simp only [BinOp.denote] at h
  case int.int => cases h; exact ⟨_, rfl⟩
  case bool.bool => cases h; exact ⟨_, rfl⟩
  case unit.unit => cases h; exact ⟨_, rfl⟩
  all_goals cases h

/-- `<>` gives a boolean, the opposite of what `=` gives. -/
theorem denote_ne {va vb v : Value} (h : BinOp.ne.denote va vb = .ok v) :
    ∃ r, v = .bool r ∧ BinOp.eq.denote va vb = .ok (.bool !r) := by
  cases va <;> cases vb <;> simp only [BinOp.denote] at h
  case int.int => cases h; exact ⟨_, rfl, by simp [BinOp.denote, bne]⟩
  case bool.bool => cases h; exact ⟨_, rfl, by simp [BinOp.denote, bne]⟩
  case unit.unit => cases h; exact ⟨_, rfl, rfl⟩
  all_goals cases h

theorem eqCmp_sound [NumDomain A] {a b : AVal A} {va vb : Value} {r : Bool}
    (ha : a.mem va) (hb : b.mem vb) (h : BinOp.eq.denote va vb = .ok (.bool r)) :
    (r = true → (eqCmp a b).1 = true) ∧ (r = false → (eqCmp a b).2 = true) := by
  cases va <;> cases vb <;> simp only [BinOp.denote] at h
  case int.int x y =>
    cases h
    have hi := cmpEq_sound (AVal.mem_int ha) (AVal.mem_int hb)
    constructor
    · intro hr
      simp [eqCmp, hi.1 (by simpa using hr)]
    · intro hr
      simp [eqCmp, hi.2 (by simpa using hr)]
  case bool.bool x y =>
    cases h
    cases x <;> cases y
    case true.true => simp [eqCmp, AVal.mem_tt ha, AVal.mem_tt hb]
    case true.false => simp [eqCmp, AVal.mem_tt ha, AVal.mem_ff hb]
    case false.true => simp [eqCmp, AVal.mem_ff ha, AVal.mem_tt hb]
    case false.false => simp [eqCmp, AVal.mem_ff ha, AVal.mem_ff hb]
  case unit.unit =>
    cases h
    simp [eqCmp, AVal.mem_unit ha, AVal.mem_unit hb]
  all_goals cases h

theorem mem_ofCmp [NumDomain A] {p : Bool × Bool} {r : Bool}
    (h : (r = true → p.1 = true) ∧ (r = false → p.2 = true)) :
    (ofCmp p : AVal A).mem (.bool r) := by
  cases r
  · exact .flat (h.2 rfl)
  · exact .flat (h.1 rfl)

theorem abinop_sound [NumDomain A] {op : BinOp} {a b : AVal A} {va vb v : Value}
    (ha : a.mem va) (hb : b.mem vb) (h : op.denote va vb = .ok v) :
    (abinop op a b).mem v := by
  cases op
  case eq =>
    obtain ⟨r, rfl⟩ := denote_eq_bool h
    exact mem_ofCmp (eqCmp_sound ha hb h)
  case ne =>
    obtain ⟨r, rfl, he⟩ := denote_ne h
    -- `<>` is `true` exactly when `=` is `false`
    have hc := eqCmp_sound ha hb he
    exact mem_ofCmp ⟨fun hr => hc.2 (by simp [hr]), fun hr => hc.1 (by simp [hr])⟩
  all_goals
    obtain ⟨x, y, rfl, rfl⟩ := denote_ints (by simp) h
    replace ha := AVal.mem_int ha
    replace hb := AVal.mem_int hb
    simp only [BinOp.denote] at h
  case add => cases h; exact .flat (add_sound ha hb)
  case sub => cases h; exact .flat (sub_sound ha hb)
  case mul => cases h; exact .flat (mul_sound ha hb)
  case div =>
    split at h
    next => cases h   -- division by zero: an error
    next hy => cases h; exact .flat (div_sound ha hb hy)
  case mod =>
    split at h
    next => cases h
    next hy => cases h; exact .flat (mod_sound ha hb hy)
  case lt => cases h; exact AVal.mem_bools (cmpLt_sound ha hb)
  case le => cases h; exact AVal.mem_bools (cmpLe_sound ha hb)
  case gt => cases h; exact AVal.mem_bools (cmpLt_sound hb ha)
  case ge => cases h; exact AVal.mem_bools (cmpLe_sound hb ha)

/-- A square is `≥ 0`. -/
theorem mul_self_nonneg (n : Int) : 0 ≤ n * n := by
  cases Int.le_total 0 n with
  | inl h => exact Int.mul_nonneg h h
  | inr h => exact Int.mul_nonneg_of_nonpos_of_nonpos h h

theorem sqInt_sound [NumDomain A] {a : A} {n : Int} (h : γ a n) : γ (sqInt a) (n * n) := by
  have hmul := mul_sound h h
  -- `n * n ≥ 0`, so `n * n` is in what `assumeLe` keeps of `top`
  have hpos := (assumeLe_sound (const_sound (A := A) 0) (top_sound (A := A) (n * n))
    (mul_self_nonneg n)).2
  exact meet_sound hmul hpos

/-- `abinopE` is sound. `hea` and `heb` are the runs of `ea` and `eb`. For `x * x`, they
    give the same value, because they look up the same name. -/
theorem abinopE_sound [NumDomain A] {op : BinOp} {ea eb : Expr} {a b : AVal A}
    {ρ : Env} {μ μ₁ μ₂ : Store} {va vb v : Value}
    (hea : Eval ρ μ ea (.ok va) μ₁) (heb : Eval ρ μ₁ eb (.ok vb) μ₂)
    (ha : a.mem va) (hb : b.mem vb) (h : op.denote va vb = .ok v) :
    (abinopE op ea eb a b).mem v := by
  unfold abinopE
  split
  next x y =>
    split
    next hxy =>
      subst hxy
      -- both sides look up `x`, so they have the same value
      cases hea with
      | var hx =>
        cases heb with
        | var hy =>
          rw [hx] at hy
          cases hy
          obtain ⟨n, m, rfl, hm⟩ := denote_ints (by simp) h
          cases hm
          simp only [BinOp.denote] at h
          cases h
          exact .flat (sqInt_sound (AVal.mem_int ha))
    next => exact abinop_sound ha hb h
  next => exact abinop_sound ha hb h

/-- If `c` evaluates to `b`, `σ.assume c b` is possible and still describes `ρ`. -/
theorem AEnv.assume_sound [NumDomain A] {σ : AEnv A} {ρ : Env} {μ μ' : Store} {c : Expr}
    {b : Bool} (hσ : σ.Describes ρ) (h : Eval ρ μ c (.ok (.bool b)) μ') :
    ∃ σ', σ.assume c b = some σ' ∧ σ'.Describes ρ := by
  cases c
  case binop op l r =>
    generalize hres : Outcome.ok (.bool b) = res at h
    cases h with
    | binop hl hr =>
      cases op
      -- arithmetic doesn't narrow
      case add | sub | mul | div | mod => exact ⟨σ, by cases b <;> rfl, hσ⟩
      -- `=` narrows when it is `true`, `<>` when it is `false`
      case eq =>
        cases b
        · exact ⟨σ, rfl, hσ⟩
        · exact refineEq_sound hσ hl hr hres.symm
      case ne =>
        cases b
        · obtain ⟨r, hr, he⟩ := denote_ne hres.symm
          cases hr
          exact refineEq_sound hσ hl hr he
        · exact ⟨σ, rfl, hσ⟩
      -- comparisons: both sides are integers, and `hd` says how they compare
      all_goals
        obtain ⟨x, y, rfl, rfl⟩ := denote_ints (by simp) hres.symm
        cases b <;> simp [BinOp.denote] at hres <;> simp only [assume]
      case lt.true  => exact refineLt_sound hσ hl hr hres
      case lt.false => exact refineLe_sound hσ hr hl (by omega)
      case le.true  => exact refineLe_sound hσ hl hr hres
      case le.false => exact refineLt_sound hσ hr hl (by omega)
      case gt.true  => exact refineLt_sound hσ hr hl hres
      case gt.false => exact refineLe_sound hσ hl hr (by omega)
      case ge.true  => exact refineLe_sound hσ hr hl hres
      case ge.false => exact refineLt_sound hσ hl hr (by omega)
    | _ => cases hres
  -- any other condition doesn't narrow
  all_goals exact ⟨σ, by cases b <;> rfl, hσ⟩

theorem joinOpt_sound_l [NumDomain A] {a : AVal A} {o : Option (AVal A)} {v : Value}
    (h : a.mem v) : (joinOpt (some a) o).mem v := by
  cases o
  · exact h
  · exact AVal.mem_join_l h

theorem joinOpt_sound_r [NumDomain A] {a : AVal A} {o : Option (AVal A)} {v : Value}
    (h : a.mem v) : (joinOpt o (some a)).mem v := by
  cases o
  · exact h
  · exact AVal.mem_join_r h

/-- A check against `R` and `F` still holds against an `R'` containing `R` and an
    `F'` that is `false` only if `F` is. -/
theorem Checked.mono [NumDomain A] {H : Hints A} {R R' : Flat A} {F F' : Bool}
    (hR : R.sub R') (hF : F' = false → F = false) {σ : AEnv A} {b : Expr}
    {Ps : List (Flat A)} (h : Checked H σ b Ps R F) : Checked H σ b Ps R' F' := by
  induction Ps generalizing σ b with
  | nil =>
    simp only [Checked] at h ⊢
    exact ⟨fun w hw => hR w (h.1 w hw), fun h' => h.2 (hF h')⟩
  | cons P Ps ih =>
    cases b
    case lam y b' => exact ih h
    -- any other body: `Checked` is `False`
    all_goals simp only [Checked] at h

/-- What `aeval` does on `fun x -> fun y -> b`. It analyses `fun y -> b` with `x` in
    its precondition. Then it puts the precondition of `x` in front of the
    preconditions of the summary of `fun y -> b`. -/
theorem aeval_lam_lam [NumDomain A] {H : Hints A} {σ : AEnv A} {x y : String}
    {b : Expr} :
    aeval H σ (.lam x (.lam y b)) =
      match (aeval H ((x, AVal.ofFlat (H.param x)) :: σ) (.lam y b)).sum with
      | some T => AVal.summary ⟨H.param x, T.pre :: T.rest, T.res, T.fails⟩
      | none => AVal.fnV := rfl

/-- `fun x -> b` gets a summary `S` whose preconditions are the hints for `x` and for
    the parameters of the `fun`s `b` starts with. `b` passes `Checked` against `S`. -/
theorem lam_checked [NumDomain A] {H : Hints A} :
    ∀ (b : Expr) {σ : AEnv A} {x : String}, ∃ S, (aeval H σ (.lam x b)).sum = some S ∧
      S.pre = H.param x ∧ S.rest = restPres H b ∧
      Checked H (bodyEnv none x S σ) b S.rest S.res S.fails := by
  intro b
  induction b with
  | lam y b' ih =>
    intro σ x
    -- the summary of the inner `fun`, with `x` in front
    obtain ⟨T, hT, hpre, hrest, hchk⟩ := ih (σ := (x, AVal.ofFlat (H.param x)) :: σ) (x := y)
    refine ⟨⟨H.param x, T.pre :: T.rest, T.res, T.fails⟩, ?_, rfl, ?_, ?_⟩
    · rw [aeval_lam_lam, hT]
      rfl
    · simp only [restPres, hpre, hrest]
    · -- checking `fun y -> b'` against it is checking `b'` against `T`
      exact hchk
  -- a body that isn't a `fun`: the result and `fails` are the body's
  | _ =>
    intro σ x
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    exact ⟨Flat.sub_refl _, id⟩

/-- The result of the last body of `b`, after the `fun`s it starts with. -/
def lastRes [NumDomain A] (H : Hints A) (σ : AEnv A) (b : Expr) : Flat A :=
  lastResOf b (aeval H σ b)

/-- Whether the last body of `b`, after the `fun`s it starts with, may fail. -/
def lastFails [NumDomain A] (H : Hints A) (σ : AEnv A) (b : Expr) : Bool :=
  lastFailsOf b (aeval H σ b) (mayFail H σ b)

/-- `b` passes the checks against its own analysis. -/
theorem checked_last [NumDomain A] {H : Hints A} {σ : AEnv A} {b : Expr} :
    Checked H σ b (restPres H b) (lastRes H σ b) (lastFails H σ b) := by
  cases b
  case lam y b' =>
    obtain ⟨T, hT, hpre, hrest, hchk⟩ := lam_checked (H := H) b' (σ := σ) (x := y)
    simp only [lastRes, lastFails, lastResOf, lastFailsOf, Expr.isLam, hT, Option.map_some, Option.getD_some,
      ↓reduceIte, restPres]
    rw [← hpre, ← hrest]
    exact hchk
  all_goals
    simp only [lastRes, lastFails, lastResOf, lastFailsOf, Expr.isLam, restPres, Bool.false_eq_true, ↓reduceIte]
    exact ⟨Flat.sub_refl _, id⟩

/-- `apply` describes the value of a call whose body evaluates to `v` (`hev`).
    `hb` says `aeval` describes `v` (induction hypothesis). -/
theorem apply_sound [NumDomain A] {af aa : AVal A} {s : Option String} {x : String}
    {b : Expr} {ρ' : Env} {va v : Value} {μ μ' : Store}
    (hf : af.mem (.clos s x b ρ')) (ha : aa.mem va)
    (hev : Eval (callEnv s x b ρ' va) μ b (.ok v) μ')
    (hb : ∀ (H : Hints A) (σ : AEnv A), σ.Describes (callEnv s x b ρ' va) →
      σ.Bound (callEnv s x b ρ' va) → (aeval H σ b).mem v) :
    (apply false af aa).mem v := by
  unfold apply
  split
  next S hS =>
    split
    next hcall =>
      simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hcall
      cases hf with
      | flat hf =>
        -- "any closure" is impossible, since `af.fn = false`: `hf` is `False`
        simp [Flat.mem, hcall.1] at hf
      | list _ hm _ => exact hm.elim   -- a closure is not a list
      | @sum _ _ S₀ _ _ _ _ H σ hS' hP hPs hR hF hd hB hchk =>
        -- the closure's summary is `S`
        rw [hS] at hS'
        cases hS'
        -- the argument meets `S.pre`, so the precondition `S₀.pre` the body was
        -- checked with
        have hv := hP va (Flat.mem_leq (AVal.mem_flat ha) hcall.2)
        have hd' := AEnv.Describes.body hd hB hchk hv
        split
        next hrest =>
          -- no more parameters: the body was checked against `S₀.res`
          have h0 : S₀.rest = [] := by
            rw [hrest] at hPs
            cases h : S₀.rest with
            | nil => rfl
            | cons _ _ => rw [h] at hPs; exact hPs.elim
          have hchk' := hchk
          rw [h0] at hchk'
          simp only [Checked] at hchk'
          have hres := hb H _ hd' (AEnv.Bound.body hB)
          exact .flat (hR v (hchk'.1 v (AVal.mem_flat hres)))
        next P Ps hrest =>
          -- more parameters: `S₀` has them too
          obtain ⟨P₀, Ps₀, h0, hP₀, hPs₀⟩ :
              ∃ P₀ Ps₀, S₀.rest = P₀ :: Ps₀ ∧ P.sub P₀ ∧ Flat.subs Ps Ps₀ := by
            rw [hrest] at hPs
            cases h : S₀.rest with
            | nil => rw [h] at hPs; exact hPs.elim
            | cons P₀ Ps₀ => rw [h] at hPs; exact ⟨P₀, Ps₀, rfl, hPs.1, hPs.2⟩
          have hchk' := hchk
          rw [h0] at hchk'
          -- so the body is a `fun`, whose value is the closure for them
          cases b
          case lam y b' =>
            cases hev
            exact .sum (S₀ := ⟨P₀, Ps₀, S₀.res, S₀.fails⟩) H _ rfl hP₀ hPs₀ hR hF hd'
              (AEnv.Bound.body hB) hchk'
          all_goals exact hchk'.elim
    next => exact AVal.mem_top _
  next => exact AVal.mem_top _

/-- The value `aeval` gives `f` in `let rec f x = b in ...` (see `aevalM`). -/
def letrecVal [NumDomain A] (H : Hints A) (σ : AEnv A) (f x : String) (b : Expr) :
    AVal A :=
  let P := H.param x
  let Ps := restPres H b
  let R := H.result f
  let env (F : Bool) := (x, AVal.ofFlat P) :: (f, AVal.summary ⟨P, Ps, R, F⟩) :: σ
  let fails := lastFails H (env false) b
  let S : Summary A := ⟨P, Ps, R, fails⟩
  if false || (lastRes H (env fails) b).leq R then AVal.summary S else AVal.fnV

/-- The value of `f` in `let rec f x = b in ...` describes its closure. -/
theorem letrecVal_mem [NumDomain A] {H : Hints A} {σ : AEnv A} {ρ : Env} {f x : String}
    {b : Expr} (hσ : σ.Describes ρ) (hB : σ.Bound ρ) :
    (letrecVal H σ f x b).mem (.clos (some f) x b ρ) := by
  dsimp only [letrecVal]
  split
  next hholds =>
    -- the summary: the last body's result was checked against the claim
    refine .sum H σ rfl (Flat.sub_refl _) (Flat.subs_refl _) (Flat.sub_refl _) id hσ hB ?_
    refine Checked.mono (fun w hw => Flat.mem_leq hw hholds) ?_ checked_last
    -- if `fails` is `false`, the body was checked assuming that the recursive
    -- calls don't fail, which is this summary
    intro hF
    simp only at hF
    rw [hF]
    exact hF
  next =>
    -- `fnV`: any closure
    exact .flat rfl

/-- Soundness, for any outcome `r`: by induction on the evaluation, so that a call's
    body, whose evaluation is part of the call's, can use the induction hypothesis. -/
theorem aeval_sound_aux [NumDomain A] {ρ : Env} {μ μ' : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ') :
    ∀ {H : Hints A} {σ : AEnv A} {v : Value}, σ.Describes ρ → σ.Bound ρ → r = .ok v →
      (aeval H σ e).mem v := by
  induction h with
  | int => intro H σ v hσ hB hr; cases hr; exact .flat (const_sound _)
  | bool => intro H σ v hσ hB hr; cases hr; exact AVal.mem_bool _
  | unit => intro H σ v hσ hB hr; cases hr; exact .flat rfl
  | nil => intro H σ v hσ hB hr; cases hr; exact .list (e := Flat.bot) rfl trivial (fun _ => rfl)
  | cons _ _ hl iha ihb =>
    intro H σ v hσ hB hr
    cases hr
    exact AVal.mem_cons (iha hσ hB rfl) (ihb hσ hB rfl) hl
  | matchNil _ _ ihs ihn =>
    intro H σ v hσ hB hr
    -- the list is `[]`, so the `[]` branch is taken
    have hnil : (aevalM false H σ _).mayBeNil = true := AVal.mayBeNil_of_mem (ihs hσ hB rfl)
    simp only [aeval, aevalM, hnil, ↓reduceIte]
    exact joinOpt_sound_l (ihn hσ hB hr)
  | @matchCons _ _ _ _ _ _ xs x _ _ _ _ _ _ ihs ihc =>
    intro H σ v hσ hB hr
    -- `x` is in the heads of the list, and `xs` in its tails
    have hs := ihs (H := H) hσ hB rfl
    have hd := (hσ.cons (x := x) (AVal.mem_ofFlat (AVal.mem_heads hs))).cons (x := xs)
      (AVal.mem_tails hs)
    -- the list has a first element, so the `::` branch is taken
    have hcons : (aevalM false H σ _).heads.leq Flat.bot = false := AVal.heads_not_bot hs
    simp only [aeval, aevalM, hcons, Bool.false_eq_true, ↓reduceIte]
    exact joinOpt_sound_r (ihc hd hB.cons.cons hr)
  | var hx => intro H σ v hσ hB hr; cases hr; exact hσ _ _ hx
  | @lam _ _ x b =>
    intro H σ v hσ hB hr
    cases hr
    -- the body was checked against the summary
    obtain ⟨S, hS, _, _, hchk⟩ := lam_checked (H := H) b (σ := σ) (x := x)
    exact .sum H σ hS (Flat.sub_refl _) (Flat.subs_refl _) (Flat.sub_refl _) id hσ hB hchk
  | app _ _ hbody ihf iha ihb =>
    intro H σ v hσ hB hr
    cases hr
    exact apply_sound (ihf hσ hB rfl) (iha hσ hB rfl) hbody (fun _ _ hd hb => ihb hd hb rfl)
  | binop hea heb iha ihb =>
    intro H σ v hσ hB hr
    exact abinopE_sound hea heb (iha hσ hB rfl) (ihb hσ hB rfl) hr
  | letin _ _ ih1 ih2 =>
    intro H σ v hσ hB hr
    exact ih2 (hσ.cons (ih1 hσ hB rfl)) hB.cons hr
  | letrec _ ih2 =>
    intro H σ v hσ hB hr
    exact ih2 (hσ.cons (letrecVal_mem hσ hB)) hB.cons hr
  | ifT hc _ ihc iht =>
    intro H σ v hσ hB hr
    have htt : (aevalM false H σ _).tt = true := AVal.mem_tt (ihc hσ hB rfl)
    obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
    simp only [aeval, aevalM, htt, hst, Option.map_some, ↓reduceIte]
    exact joinOpt_sound_l (iht hdt (AEnv.assume_bound hB hst) hr)
  | ifF hc _ ihc ihe =>
    intro H σ v hσ hB hr
    have hff : (aevalM false H σ _).ff = true := AVal.mem_ff (ihc hσ hB rfl)
    obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
    simp only [aeval, aevalM, hff, hse, Option.map_some, ↓reduceIte]
    exact joinOpt_sound_r (ihe hde (AEnv.assume_bound hB hse) hr)
  | assert | exn => intro H σ v hσ hB hr; cases hr; exact .flat rfl
  -- the rules giving an error: no value
  | varErr | appNotFn | appErrF | appErrA | letinErr | ifNotBool | ifErr
  | binopErrL | binopErrR | consNotList | consErrL | consErrR | matchNotList | matchErr
  | assertF | assertNotBool | assertErr | exnErr | raise | raiseNotExn | raiseErr =>
    intro H σ v hσ hB hr
    cases hr
  -- the expressions not analysed yet: `top`
  | _ => intro H σ v hσ hB hr; exact AVal.mem_top _

/-- **Soundness**: if `e` evaluates to `v`, `aeval` describes `v`, whatever the
    hints. -/
theorem aeval_sound [NumDomain A] {H : Hints A} {σ : AEnv A} {ρ : Env} {μ μ' : Store}
    {e : Expr} {v : Value} (hσ : σ.Describes ρ) (hB : σ.Bound ρ)
    (h : Eval ρ μ e (.ok v) μ') : (aeval H σ e).mem v :=
  aeval_sound_aux h hσ hB rfl

/-- A recursive closure of one parameter whose summary was checked against its body
    satisfies it. -/
theorem letrec_sat [NumDomain A] {H : Hints A} {σ : AEnv A} {ρ : Env} {f x : String}
    {b : Expr} {S : Summary A} (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (hrest : S.rest = [])
    (hchk : Checked H (bodyEnv (some f) x S σ) b S.rest S.res S.fails) :
    Sat S (some f) x b ρ := by
  intro v w μ μ' hv hev
  -- the body is checked in an abstract environment describing the call's
  have hd := AEnv.Describes.body hσ hB hchk hv
  have hchk' := hchk
  rw [hrest] at hchk'
  simp only [Checked] at hchk'
  exact hchk'.1 w (AVal.mem_flat (aeval_sound hd (AEnv.Bound.body hB) hev))

end Diva.AbsInt
