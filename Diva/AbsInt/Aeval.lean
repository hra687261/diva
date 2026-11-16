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

theorem atom_sound {e : Expr} {μ μ' : Store} {v : Value} (hσ : σ.Describes ρ)
    (h : Eval ρ μ e (.ok v) μ') : (σ.atom e).mem v := by
  cases e
  case var x => cases h with | var hx => exact hσ x v hx
  case int => cases h; exact .inl (const_sound _)
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
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr (.inl hp.2)) hl (.inl hp.1)⟩

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
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr (.inl hp.2)) hl (.inl hp.1)⟩

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
  case add => cases h; exact .inl (add_sound ha hb)
  case sub => cases h; exact .inl (sub_sound ha hb)
  case mul => cases h; exact .inl (mul_sound ha hb)
  case div =>
    split at h
    next => cases h   -- division by zero: an error
    next hy => cases h; exact .inl (div_sound ha hb hy)
  case mod =>
    split at h
    next => cases h
    next hy => cases h; exact .inl (mod_sound ha hb hy)
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

/-- A call to a closure satisfying `(P, R)`, with an argument meeting `P`, gives a
    value in `R`. -/
theorem apply_sound [NumDomain A] {af aa : AVal A} {s : Option String} {x : String}
    {b : Expr} {ρ' : Env} {va v : Value} {μ μ' : Store}
    (hf : af.mem (.clos s x b ρ')) (ha : aa.mem va)
    (hb : Eval (callEnv s x b ρ' va) μ b (.ok v) μ') : (apply af aa).mem v := by
  unfold apply
  split
  next P R hS =>
    split
    next hcall =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcall
      simp only [AVal.mem] at hf
      rcases hf with hf | hf
      · -- "any closure" is impossible, since `af.fn = false`: `hf` is `False`
        simp [Flat.mem, hcall.1] at hf
      · -- the closure satisfies the summary `(P, R)`
        simp only [AVal.sumMem] at hf
        obtain ⟨S, hS', hsat⟩ := hf
        rw [hS] at hS'
        -- `hS' : some (P, R) = some S`, so `S` is `(P, R)`
        simp only [Option.some.injEq] at hS'
        subst hS'
        -- the argument meets `P`, so the result is in `R`
        have hP : P.mem va := Flat.mem_leq (AVal.mem_flat ha) hcall.2
        exact .inl (hsat va v μ μ' hP hb)
    next => exact AVal.mem_top _
  next => exact AVal.mem_top _

/-- A recursive closure whose summary was checked against its body satisfies it.
    TODO: by induction on the height of the evaluation of the body: a recursive call
    inside it is a smaller evaluation, so it satisfies the summary by induction. -/
theorem letrec_sat [NumDomain A] {H : Hints A} {σ : AEnv A} {ρ : Env} {f x : String}
    {b : Expr} {S : Summary A} (hσ : σ.Describes ρ)
    (hholds : (aeval H ((x, AVal.ofFlat S.1) :: (f, AVal.summary S) :: σ) b).flat.leq S.2
      = true) :
    Sat S (some f) x b ρ := by
  sorry

/-- **Soundness**: if `e` evaluates to `v`, `aeval` describes `v`, whatever the
    hints. -/
theorem aeval_sound [NumDomain A] {H : Hints A} {σ : AEnv A} {ρ : Env} {μ μ' : Store}
    {e : Expr} {v : Value} (hσ : σ.Describes ρ) (h : Eval ρ μ e (.ok v) μ') :
    (aeval H σ e).mem v := by
  induction e generalizing σ ρ μ μ' v with
  | int m => cases h; exact .inl (const_sound _)
  | bool b => cases h; cases b <;> exact .inl rfl
  | unit => cases h; exact .inl rfl
  | nil => cases h; exact .inl rfl
  | cons => cases h; exact .inl rfl
  | var x => cases h with | var hx => exact hσ x v hx
  | lam x b ihb =>
    cases h
    -- the closure satisfies its summary: the body was analysed with `x` in `P`
    refine .inr ⟨_, rfl, fun va w μ₁ μ₂ hv hev => ?_⟩
    exact AVal.mem_flat (ihb (hσ.cons (AVal.mem_ofFlat hv)) hev)
  | app f a ihf iha =>
    cases h with
    | app hf ha hb => exact apply_sound (ihf hσ hf) (iha hσ ha) hb
  | binop op a b iha ihb =>
    generalize hr : Outcome.ok v = r at h
    cases h with
    | binop ha hb => exact abinop_sound (iha hσ ha) (ihb hσ hb) hr.symm
    | _ => cases hr
  | letin x e1 e2 ih1 ih2 =>
    cases h with
    | letin h1 h2 => exact ih2 (hσ.cons (ih1 hσ h1)) h2
  | letrec f x e1 e2 _ ih2 =>
    cases h with
    | letrec h2 =>
      refine ih2 (hσ.cons ?_) h2
      -- `f` satisfies its summary if the check passed, and is a closure anyway
      split
      next hholds => exact .inr ⟨_, rfl, letrec_sat hσ hholds⟩
      next => exact .inl rfl
  | ite c t e ihc iht ihe =>
    cases h with
    | ifT hc ht =>
      have htt : (aeval H σ c).tt = true := AVal.mem_tt (ihc hσ hc)
      obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
      simp only [aeval, htt, hst, Option.map_some, ↓reduceIte]
      exact joinOpt_sound_l (iht hdt ht)
    | ifF hc he =>
      have hff : (aeval H σ c).ff = true := AVal.mem_ff (ihc hσ hc)
      obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
      simp only [aeval, hff, hse, Option.map_some, ↓reduceIte]
      exact joinOpt_sound_r (ihe hde he)
  | assert => cases h; exact .inl rfl
  | exn => cases h; exact .inl rfl
  | raise => cases h
  | _ => exact AVal.mem_top _

end Diva.AbsInt
