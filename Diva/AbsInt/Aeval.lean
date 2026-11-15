import Diva.AbsInt.AVal

/-!
# Abstract evaluation

`aeval σ e` over-approximates the values `e` can evaluate to (`AVal`), in any
`NumDomain`. Integers and booleans are tracked by value, the other kinds only by
kind, what isn't analysed yet (calls, the store, catching exceptions) gives `top`.

A comparison `l < r` (or `≤`, `>`, `≥`) in an `if` narrows the variables it
compares in each branch, and a branch that can't be taken is skipped. Only
variables and constants are looked at in the comparison: `x < 5` narrows `x`,
`x + 1 < 5` doesn't.
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

def aeval [NumDomain A] (σ : AEnv A) : Expr → AVal A
  | .int n => AVal.ofInt (const n)
  | .bool b => AVal.bools b !b
  | .unit => AVal.unitV
  | .nil | .cons _ _ => AVal.listV
  | .lam _ _ => AVal.fnV
  | .var x => σ.get x
  | .binop op a b => abinop op (aeval σ a) (aeval σ b)
  | .letin x e1 e2 => aeval ((x, aeval σ e1) :: σ) e2
  | .letrec f _ _ e2 => aeval ((f, AVal.fnV) :: σ) e2
  | .ite c t e =>
    -- a branch is taken only if the condition may have that value
    joinOpt
      (if (aeval σ c).tt then (σ.assume c true).map (aeval · t) else none)
      (if (aeval σ c).ff then (σ.assume c false).map (aeval · e) else none)
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
  case int => cases h; exact const_sound _
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
  have ha : γ (σ.atom l).int n := atom_sound hσ hl
  have hb : γ (σ.atom r).int m := atom_sound hσ hr
  -- `l < r` is possible, so `refineLt` narrows instead of giving `none`
  have hmay := (cmpLt_sound ha hb).1 h
  unfold refineLt
  rw [ite_eq_left hmay]
  -- the narrowed values still describe `l` and `r`
  have hp := assumeLt_sound ha hb h
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr hp.2) hl hp.1⟩

theorem refineLe_sound {l r : Expr} {μ₁ μ₂ μ₃ μ₄ : Store} {n m : Int}
    (hσ : σ.Describes ρ) (hl : Eval ρ μ₁ l (.ok (.int n)) μ₂)
    (hr : Eval ρ μ₃ r (.ok (.int m)) μ₄) (h : n ≤ m) :
    ∃ σ', σ.refineLe l r = some σ' ∧ σ'.Describes ρ := by
  have ha : γ (σ.atom l).int n := atom_sound hσ hl
  have hb : γ (σ.atom r).int m := atom_sound hσ hr
  -- `l ≤ r` is possible, so `refineLe` narrows instead of giving `none`
  have hmay := (cmpLe_sound ha hb).1 h
  unfold refineLe
  rw [ite_eq_left hmay]
  -- the narrowed values still describe `l` and `r`
  have hp := assumeLe_sound ha hb h
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr hp.2) hl hp.1⟩

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
    simp only [BinOp.denote] at h
  case add => cases h; exact add_sound ha hb
  case sub => cases h; exact sub_sound ha hb
  case mul => cases h; exact mul_sound ha hb
  case div =>
    split at h
    next => cases h   -- division by zero: an error
    next hy => cases h; exact div_sound ha hb hy
  case mod =>
    split at h
    next => cases h
    next hy => cases h; exact mod_sound ha hb hy
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

/-- **Soundness**: if `e` evaluates to `v`, `aeval` describes `v`. -/
theorem aeval_sound [NumDomain A] {σ : AEnv A} {ρ : Env} {μ μ' : Store} {e : Expr}
    {v : Value} (hσ : σ.Describes ρ) (h : Eval ρ μ e (.ok v) μ') :
    (aeval σ e).mem v := by
  induction e generalizing σ ρ μ μ' v with
  | int m => cases h; exact const_sound _
  | bool b => cases h; cases b <;> rfl
  | unit => cases h; rfl
  | nil => cases h; rfl
  | cons => cases h; rfl
  | lam => cases h; rfl
  | var x => cases h with | var hx => exact hσ x v hx
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
      refine ih2 ?_ h2
      exact hσ.cons rfl   -- `f` is a closure
  | ite c t e ihc iht ihe =>
    cases h with
    | ifT hc ht =>
      have htt : (aeval σ c).tt = true := ihc hσ hc
      obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
      simp only [aeval, htt, hst, Option.map_some, ↓reduceIte]
      exact joinOpt_sound_l (iht hdt ht)
    | ifF hc he =>
      have hff : (aeval σ c).ff = true := ihc hσ hc
      obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
      simp only [aeval, hff, hse, Option.map_some, ↓reduceIte]
      exact joinOpt_sound_r (ihe hde he)
  | assert => cases h; rfl
  | exn => cases h; rfl
  | raise => cases h
  | _ => exact AVal.mem_top _

end Diva.AbsInt
