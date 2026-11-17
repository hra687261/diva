import Diva.AbsInt.AVal

/-!
# Abstract evaluation

`aeval H σ e` over-approximates the values `e` can evaluate to (`AVal`), in any
`NumDomain`. Integers and booleans are tracked by value, the other kinds only by
kind; what isn't analysed yet (the store, catching exceptions) gives `top`.

A comparison `l < r` (or `≤`, `>`, `≥`) in an `if` narrows the variables it
compares in each branch, and a branch that can't be taken is skipped. Only
variables and constants are looked at in the comparison: `x < 5` narrows `x`,
`x + 1 < 5` doesn't.

Functions are not iterated: the hints `H` claim each parameter's range `P` and each
recursive function's result `R`, and `aeval` only checks these claims.
- `fun x -> b` gives the summary `(P, R)`, where `R` is `b` analysed with `x ∈ P`.
- A call gives `R` if the argument is in `P`, and `⊤` otherwise.
- `let rec f` keeps its claimed `R` only if the body, assuming `R` for the
  recursive calls, stays in `R`.
A wrong claim gives `⊤`.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

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

/-- Record `a` for `e` if it is a variable. -/
def bind (σ : AEnv A) : Expr → AVal A → AEnv A
  | .var x, a => (x, a) :: σ
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

/-- `σ` narrowed by `c` evaluating to `b`, or `none` if it can't. -/
def assume (σ : AEnv A) : Expr → Bool → Option (AEnv A)
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
  | .eq, _, _ | .ne, _, _ => AVal.top   -- not analysed yet

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

/-- A call: the summary's result, if the function is certainly described by its
    summary and the argument meets the precondition, anything otherwise. -/
def apply [NumDomain A] (af aa : AVal A) : AVal A :=
  match af.sum with
  | some (P, R) => if !af.fn && aa.flat.leq P then AVal.ofFlat R else AVal.top
  | none => AVal.top

def aeval [NumDomain A] (H : Hints A) (σ : AEnv A) : Expr → AVal A
  | .int n => AVal.ofInt (const n)
  | .bool b => AVal.bools b !b
  | .unit => AVal.unitV
  | .nil | .cons _ _ => AVal.listV
  | .var x => σ.get x
  | .binop op a b => abinop op (aeval H σ a) (aeval H σ b)
  | .letin x e1 e2 => aeval H ((x, aeval H σ e1) :: σ) e2
  | .lam x b =>
    -- the body, analysed with `x` in its precondition
    let P := H.param x
    AVal.summary (P, (aeval H ((x, AVal.ofFlat P) :: σ) b).flat)
  | .app f a => apply (aeval H σ f) (aeval H σ a)
  | .letrec f x b e2 =>
    -- the claimed summary, checked against the body (which may call `f`)
    let S : Summary A := (H.param x, H.result f)
    let holds := (aeval H ((x, AVal.ofFlat S.1) :: (f, AVal.summary S) :: σ) b).flat.leq S.2
    aeval H ((f, if holds then AVal.summary S else AVal.fnV) :: σ) e2
  | .ite c t e =>
    -- a branch is taken only if the condition may have that value
    joinOpt
      (if (aeval H σ c).tt then (σ.assume c true).map (aeval H · t) else none)
      (if (aeval H σ c).ff then (σ.assume c false).map (aeval H · e) else none)
  | .assert _ => AVal.unitV
  | .exn _ _ => AVal.exnV
  | .raise _ => AVal.bot   -- never gives a value
  | _ => AVal.top

/-! ## Concretisation -/

/-- The abstract environment a closure's body is checked in, against the summary
    `S`: `x` in the precondition and, for a recursive function, `f` with `S`. -/
def bodyEnv [NumDomain A] (s : Option String) (x : String) (S : Summary A) (σ : AEnv A) :
    AEnv A :=
  match s with
  | none => (x, AVal.ofFlat S.1) :: σ
  | some f => (x, AVal.ofFlat S.1) :: (f, AVal.summary S) :: σ

/-- Concretisation: the values `a` describes.

    A closure is described by `a`'s summary `(P, R)` if its body was checked
    against a summary `(P₀, R₀)` at least as strong, in an abstract environment `σ`
    describing the closure's own. This records the check rather than stating `Sat`
    directly: soundness can then be proved by induction on the evaluation, and `Sat`
    follows (`letrec_sat`). -/
inductive AVal.mem {A : Type} [NumDomain A] : AVal A → Value → Prop where
  | flat {a : AVal A} {v : Value} : a.toFlat.mem v → AVal.mem a v
  | sum {a : AVal A} {P R P₀ R₀ : Flat A} {s : Option String} {x : String} {b : Expr}
      {ρ : Env} (H : Hints A) (σ : AEnv A) :
      a.sum = some (P, R) → P.sub P₀ → R₀.sub R →
      -- `σ` describes `ρ`
      (∀ y w, ρ.lookup y = some w → AVal.mem (σ.get y) w) →
      -- the body's result is in `R₀`
      (aeval H (bodyEnv s x (P₀, R₀) σ) b).flat.sub R₀ →
      AVal.mem a (.clos s x b ρ)

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

theorem mem_tt {a : AVal A} (h : a.mem (.bool true)) : a.tt = true := by
  cases h with
  | flat h => exact h

theorem mem_ff {a : AVal A} (h : a.mem (.bool false)) : a.ff = true := by
  cases h with
  | flat h => exact h

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

theorem mem_join_l {a b : AVal A} {v : Value} (h : a.mem v) : (a.join b).mem v := by
  unfold join
  split
  next S T hS hT =>
    split
    next hpre =>
      cases h with
      | flat h => exact .flat (Flat.mem_join_l h)
      | sum H σ hS' hP hR hd hb =>
        -- `S` is the closure's summary `(P, R)`; `R ⊆ R ⊔ T.2`
        rw [hS] at hS'
        simp only [Option.some.injEq] at hS'
        subst hS'
        exact .sum H σ rfl hP (fun w hw => Flat.mem_join_l (hR w hw)) hd hb
    next => exact .flat (Flat.mem_join_l (mem_flat h))
  next S hS hT =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_l h)
    | sum H σ hS' hP hR hd hb =>
      -- the summary is kept
      rw [hS] at hS'
      exact .sum H σ hS' hP hR hd hb
  next _ _ hS =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_l h)
    | sum _ _ hS' =>
      -- `a` has no summary
      rw [hS] at hS'
      cases hS'

theorem mem_join_r {a b : AVal A} {v : Value} (h : b.mem v) : (a.join b).mem v := by
  unfold join
  split
  next S T hS hT =>
    split
    next hpre =>
      simp only [Bool.and_eq_true] at hpre
      cases h with
      | flat h => exact .flat (Flat.mem_join_r h)
      | sum H σ hT' hP hR hd hb =>
        -- `T` is the closure's summary `(P, R)`; `S.1 ⊆ P` and `R ⊆ S.2 ⊔ R`
        rw [hT] at hT'
        simp only [Option.some.injEq] at hT'
        subst hT'
        have hP' : S.1.sub _ := fun w hw => hP w (Flat.mem_leq hw hpre.1)
        exact .sum H σ rfl hP' (fun w hw => Flat.mem_join_r (hR w hw)) hd hb
    next => exact .flat (Flat.mem_join_r (mem_flat h))
  next S hS hT =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_r h)
    | sum _ _ hT' =>
      -- `b` has no summary
      rw [hT] at hT'
      cases hT'
  next =>
    cases h with
    | flat h => exact .flat (Flat.mem_join_r h)
    | sum H σ hT' hP hR hd hb =>
      -- the summary is kept
      exact .sum H σ hT' hP hR hd hb

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

/-- A closure's body is checked in an abstract environment that describes its call
    environment, if the argument meets the precondition. -/
theorem Describes.body {H : Hints A} {s : Option String} {x : String} {b : Expr}
    {P₀ R₀ : Flat A} {va : Value} (hσ : σ.Describes ρ)
    (hb : (aeval H (bodyEnv s x (P₀, R₀) σ) b).flat.sub R₀) (hv : P₀.mem va) :
    (bodyEnv s x (P₀, R₀) σ).Describes (callEnv s x b ρ va) := by
  cases s
  case none => exact hσ.cons (.flat hv)
  case some f =>
    -- `f` is the closure itself, described by its summary by the same check
    have hf : (AVal.summary (P₀, R₀)).mem (.clos (some f) x b ρ) :=
      .sum H σ rfl (Flat.sub_refl _) (Flat.sub_refl _) hσ hb
    exact (hσ.cons hf).cons (.flat hv)

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
      intro y w hy
      by_cases hxy : x = y
      · subst hxy
        rw [hx] at hy; cases hy
        simpa [get, bind, List.lookup] using ha
      · have hyx : (y == x) = false := by simp; exact Ne.symm hxy
        simpa [get, bind, List.lookup, hyx] using hσ y w hy
  all_goals exact hσ

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

theorem abinop_sound [NumDomain A] {op : BinOp} {a b : AVal A} {va vb v : Value}
    (ha : a.mem va) (hb : b.mem vb) (h : op.denote va vb = .ok v) :
    (abinop op a b).mem v := by
  cases op
  case eq | ne => exact AVal.mem_top _
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
      -- arithmetic and `=`, `<>` don't narrow
      case add | sub | mul | div | mod | eq | ne => exact ⟨σ, by cases b <;> rfl, hσ⟩
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

/-- A call to a closure described by `(P, R)`, with an argument meeting `P`, gives a
    value in `R`. `hb`: the body's evaluation is described by any check of it (the
    induction hypothesis of `aeval_sound_aux`). -/
theorem apply_sound [NumDomain A] {af aa : AVal A} {s : Option String} {x : String}
    {b : Expr} {ρ' : Env} {va v : Value}
    (hf : af.mem (.clos s x b ρ')) (ha : aa.mem va)
    (hb : ∀ (H : Hints A) (σ : AEnv A), σ.Describes (callEnv s x b ρ' va) →
      (aeval H σ b).mem v) :
    (apply af aa).mem v := by
  unfold apply
  split
  next P R hS =>
    split
    next hcall =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcall
      cases hf with
      | flat hf =>
        -- "any closure" is impossible, since `af.fn = false`: `hf` is `False`
        simp [Flat.mem, hcall.1] at hf
      | sum H σ hS' hP hR hd hcheck =>
        -- `hS' : some (P, R) = some (P', R')`, so the closure's summary is `(P, R)`
        rw [hS] at hS'
        simp only [Option.some.injEq, Prod.mk.injEq] at hS'
        obtain ⟨rfl, rfl⟩ := hS'
        -- the argument meets `P`, so the precondition `P₀` the body was checked with
        have hv := hP va (Flat.mem_leq (AVal.mem_flat ha) hcall.2)
        -- so the result is in `R₀`, so in `R`
        have hres := hb H _ (AEnv.Describes.body hd hcheck hv)
        exact .flat (hR v (hcheck v (AVal.mem_flat hres)))
    next => exact AVal.mem_top _
  next => exact AVal.mem_top _

/-- Soundness, for any outcome `r`: by induction on the evaluation, so that a call's
    body, whose evaluation is part of the call's, can use the induction hypothesis. -/
theorem aeval_sound_aux [NumDomain A] {ρ : Env} {μ μ' : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ') :
    ∀ {H : Hints A} {σ : AEnv A} {v : Value}, σ.Describes ρ → r = .ok v →
      (aeval H σ e).mem v := by
  induction h with
  | int => intro H σ v hσ hr; cases hr; exact .flat (const_sound _)
  | bool => intro H σ v hσ hr; cases hr; exact AVal.mem_bool _
  | unit | nil => intro H σ v hσ hr; cases hr; exact .flat rfl
  | cons => intro H σ v hσ hr; cases hr; exact .flat rfl
  | var hx => intro H σ v hσ hr; cases hr; exact hσ _ _ hx
  | lam =>
    intro H σ v hσ hr
    cases hr
    -- the body was checked with `x` in `P`, and its result is the summary's
    exact .sum H σ rfl (Flat.sub_refl _) (Flat.sub_refl _) hσ (Flat.sub_refl _)
  | app _ _ _ ihf iha ihb =>
    intro H σ v hσ hr
    exact apply_sound (ihf hσ rfl) (iha hσ rfl) (fun _ _ hd => ihb hd hr)
  | binop _ _ iha ihb =>
    intro H σ v hσ hr
    exact abinop_sound (iha hσ rfl) (ihb hσ rfl) hr
  | letin _ _ ih1 ih2 =>
    intro H σ v hσ hr
    exact ih2 (hσ.cons (ih1 hσ rfl)) hr
  | letrec _ ih2 =>
    intro H σ v hσ hr
    refine ih2 (hσ.cons ?_) hr
    -- `f` is described by its summary if the check passed, and is a closure anyway
    split
    next hholds => exact .sum H σ rfl (Flat.sub_refl _) (Flat.sub_refl _) hσ
                     (fun w hw => Flat.mem_leq hw hholds)
    next => exact .flat rfl
  | ifT hc _ ihc iht =>
    intro H σ v hσ hr
    have htt : (aeval H σ _).tt = true := AVal.mem_tt (ihc hσ rfl)
    obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
    simp only [aeval, htt, hst, Option.map_some, ↓reduceIte]
    exact joinOpt_sound_l (iht hdt hr)
  | ifF hc _ ihc ihe =>
    intro H σ v hσ hr
    have hff : (aeval H σ _).ff = true := AVal.mem_ff (ihc hσ rfl)
    obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
    simp only [aeval, hff, hse, Option.map_some, ↓reduceIte]
    exact joinOpt_sound_r (ihe hde hr)
  | assert | exn => intro H σ v hσ hr; cases hr; exact .flat rfl
  -- the rules giving an error: no value
  | varErr | appNotFn | appErrF | appErrA | letinErr | ifNotBool | ifErr
  | binopErrL | binopErrR | consNotList | consErrL | consErrR
  | assertF | assertNotBool | assertErr | exnErr | raise | raiseNotExn | raiseErr =>
    intro H σ v hσ hr
    cases hr
  -- the expressions not analysed yet: `top`
  | _ => intro H σ v hσ hr; exact AVal.mem_top _

/-- **Soundness**: if `e` evaluates to `v`, `aeval` describes `v`, whatever the
    hints. -/
theorem aeval_sound [NumDomain A] {H : Hints A} {σ : AEnv A} {ρ : Env} {μ μ' : Store}
    {e : Expr} {v : Value} (hσ : σ.Describes ρ) (h : Eval ρ μ e (.ok v) μ') :
    (aeval H σ e).mem v :=
  aeval_sound_aux h hσ rfl

/-- A recursive closure whose summary was checked against its body satisfies it. -/
theorem letrec_sat [NumDomain A] {H : Hints A} {σ : AEnv A} {ρ : Env} {f x : String}
    {b : Expr} {S : Summary A} (hσ : σ.Describes ρ)
    (hholds : (aeval H ((x, AVal.ofFlat S.1) :: (f, AVal.summary S) :: σ) b).flat.leq S.2
      = true) :
    Sat S (some f) x b ρ := by
  intro v w μ μ' hv hev
  -- the check, as an inclusion
  have hcheck : (aeval H (bodyEnv (some f) x (S.1, S.2) σ) b).flat.sub S.2 :=
    fun u hu => Flat.mem_leq hu hholds
  -- the body is checked in an abstract environment describing the call's
  have hd := AEnv.Describes.body hσ hcheck hv
  exact hcheck w (AVal.mem_flat (aeval_sound hd hev))

end Diva.AbsInt
