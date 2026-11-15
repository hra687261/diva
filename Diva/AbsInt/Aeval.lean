import Diva.AbsInt.Framework
import Diva.Semantics

/-!
# Abstract evaluation of integer expressions

`aeval σ e` over-approximates the integers `e` can evaluate to, in any
`NumDomain`. Only the integers are analysed, anything else gives `top`.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

/-- Abstract environment: what is known about the integer variables. -/
abbrev AEnv (A : Type) := List (String × A)

namespace AEnv

variable [NumDomain A]

/-- What `σ` knows about `x` (`top` if nothing). -/
def get (σ : AEnv A) (x : String) : A := (σ.lookup x).getD top

/-- What `σ` knows about a variable or a constant (`top` for anything else). -/
def atom (σ : AEnv A) : Expr → A
  | .var x => σ.get x
  | .int k => const k
  | _ => top

/-- Record `a` for `e` if it is a variable. -/
def bind (σ : AEnv A) : Expr → A → AEnv A
  | .var x, a => (x, a) :: σ
  | _, _ => σ

/-- `σ` narrowed by `l < r`, or `none` if `l < r` can't hold. -/
def refineLt (σ : AEnv A) (l r : Expr) : Option (AEnv A) :=
  if (cmpLt (σ.atom l) (σ.atom r)).1 then
    let p := assumeLt (σ.atom l) (σ.atom r)
    some ((σ.bind r p.2).bind l p.1)
  else none

/-- `σ` narrowed by `l ≤ r`, or `none` if `l ≤ r` can't hold. -/
def refineLe (σ : AEnv A) (l r : Expr) : Option (AEnv A) :=
  if (cmpLe (σ.atom l) (σ.atom r)).1 then
    let p := assumeLe (σ.atom l) (σ.atom r)
    some ((σ.bind r p.2).bind l p.1)
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

/-- Join the results of the branches that can be taken (`none`: dead branch). -/
def joinOpt [NumDomain A] : Option A → Option A → A
  | some a, some b => join a b
  | some a, none => a
  | none, some b => b
  | none, none => bot

def aeval [NumDomain A] (σ : AEnv A) : Expr → A
  | .int n => const n
  | .var x => σ.get x
  | .binop .add a b => add (aeval σ a) (aeval σ b)
  | .binop .sub a b => sub (aeval σ a) (aeval σ b)
  | .binop .mul a b => mul (aeval σ a) (aeval σ b)
  | .binop .div a b => div (aeval σ a) (aeval σ b)
  | .binop .mod a b => mod (aeval σ a) (aeval σ b)
  | .letin x e1 e2 => aeval ((x, aeval σ e1) :: σ) e2
  | .ite c t e =>
    joinOpt ((σ.assume c true).map (aeval · t)) ((σ.assume c false).map (aeval · e))
  | _ => top

/-! ## Soundness -/

/-- `σ` describes the integers of `ρ`. -/
def AEnv.Describes [NumDomain A] (σ : AEnv A) (ρ : Env) : Prop :=
  ∀ x n, ρ.lookup x = some (.int n) → γ (σ.get x) n

namespace AEnv

variable [NumDomain A] {σ : AEnv A} {ρ : Env}

/-- If `σ` describes `ρ`, adding `x ↦ a` to `σ` and `x ↦ v` to `ρ` keeps it so,
    provided `a` describes `v` whenever `v` is an integer. -/
theorem Describes.cons {x : String} {a : A} {v : Value} (hσ : σ.Describes ρ)
    (hv : ∀ k, v = .int k → γ a k) : AEnv.Describes ((x, a) :: σ) ((x, v) :: ρ) := by
  unfold AEnv.Describes
  intro y k hy
  by_cases hxy : x = y
  · subst hxy
    simp [List.lookup] at hy
    simpa [get, List.lookup] using hv k hy
  · have hyx : (y == x) = false := by simp; exact Ne.symm hxy
    simp [List.lookup, hyx] at hy
    simpa [get, List.lookup, hyx] using hσ y k hy

theorem atom_sound {e : Expr} {μ μ' : Store} {n : Int} (hσ : σ.Describes ρ)
    (h : Eval ρ μ e (.ok (.int n)) μ') : γ (σ.atom e) n := by
  cases e
  case var x => cases h with | var hx => exact hσ x n hx
  case int => cases h; exact const_sound _
  all_goals exact top_sound _

/-- Recording `a` for `e` keeps the description, if `a` describes `e`'s value. -/
theorem bind_sound {e : Expr} {a : A} {μ μ' : Store} {n : Int} (hσ : σ.Describes ρ)
    (h : Eval ρ μ e (.ok (.int n)) μ') (ha : γ a n) : (σ.bind e a).Describes ρ := by
  cases e
  case var x =>
    cases h with
    | var hx =>
      intro y k hy
      by_cases hxy : x = y
      · subst hxy
        rw [hx] at hy; cases hy
        simpa [get, bind, List.lookup] using ha
      · have hyx : (y == x) = false := by simp; exact Ne.symm hxy
        simpa [get, bind, List.lookup, hyx] using hσ y k hy
  all_goals exact hσ

theorem refineLt_sound {l r : Expr} {μ₁ μ₂ μ₃ μ₄ : Store} {n m : Int}
    (hσ : σ.Describes ρ) (hl : Eval ρ μ₁ l (.ok (.int n)) μ₂)
    (hr : Eval ρ μ₃ r (.ok (.int m)) μ₄) (h : n < m) :
    ∃ σ', σ.refineLt l r = some σ' ∧ σ'.Describes ρ := by
  have ha := atom_sound hσ hl
  have hb := atom_sound hσ hr
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
  have ha := atom_sound hσ hl
  have hb := atom_sound hσ hr
  -- `l ≤ r` is possible, so `refineLe` narrows instead of giving `none`
  have hmay := (cmpLe_sound ha hb).1 h
  unfold refineLe
  rw [ite_eq_left hmay]
  -- the narrowed values still describe `l` and `r`
  have hp := assumeLe_sound ha hb h
  exact ⟨_, rfl, bind_sound (bind_sound hσ hr hp.2) hl hp.1⟩

end AEnv

/-- An operator gives an integer only on integer operands. -/
theorem denote_int {op : BinOp} {va vb : Value} {n : Int}
    (h : op.denote va vb = .ok (.int n)) :
    ∃ x y, va = .int x ∧ vb = .int y ∧ op.denote (.int x) (.int y) = .ok (.int n) := by
  cases va <;> cases vb
  -- only two integers give an integer
  case int.int x y => exact ⟨x, y, rfl, rfl, h⟩
  all_goals cases op <;> simp [BinOp.denote] at h

/-- `<`, `≤`, `>`, `≥` give a boolean only on integer operands. -/
theorem denote_cmp {op : BinOp} {va vb : Value} {b : Bool}
    (hop : op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (h : op.denote va vb = .ok (.bool b)) :
    ∃ x y, va = .int x ∧ vb = .int y ∧ op.denote (.int x) (.int y) = .ok (.bool b) := by
  rcases hop with rfl | rfl | rfl | rfl
  all_goals
    cases va <;> cases vb
    -- only two integers give a boolean
    case int.int x y => exact ⟨x, y, rfl, rfl, h⟩
    all_goals simp [BinOp.denote] at h

/-- If `c` evaluates to `b`, `σ.assume c b` is possible and still describes `ρ`. -/
theorem AEnv.assume_sound [NumDomain A] {σ : AEnv A} {ρ : Env} {μ μ' : Store} {c : Expr}
    {b : Bool} (hσ : σ.Describes ρ) (h : Eval ρ μ c (.ok (.bool b)) μ') :
    ∃ σ', σ.assume c b = some σ' ∧ σ'.Describes ρ := by
  cases c
  case binop op l r =>
    generalize hres : Outcome.ok (.bool b) = res at h
    cases h with
    | binop hl hr =>
      cases op <;> cases b <;> simp only [assume] <;>
        first
        | exact ⟨σ, rfl, hσ⟩
        | (obtain ⟨x, y, rfl, rfl, hd⟩ := denote_cmp (by simp) hres.symm
           simp [BinOp.denote] at hd
           first
           | exact refineLt_sound hσ hl hr (by omega)
           | exact refineLt_sound hσ hr hl (by omega)
           | exact refineLe_sound hσ hl hr (by omega)
           | exact refineLe_sound hσ hr hl (by omega))
    | _ => cases hres
  all_goals exact ⟨σ, by cases b <;> rfl, hσ⟩

theorem joinOpt_sound_l [NumDomain A] {a : A} {o : Option A} {n : Int} (h : γ a n) :
    γ (joinOpt (some a) o) n := by
  cases o
  · exact h
  · exact join_sound_l h

theorem joinOpt_sound_r [NumDomain A] {a : A} {o : Option A} {n : Int} (h : γ a n) :
    γ (joinOpt o (some a)) n := by
  cases o
  · exact h
  · exact join_sound_r h

/-- **Soundness**: if `e` evaluates to the integer `n`, `aeval` describes `n`. -/
theorem aeval_sound [NumDomain A] {σ : AEnv A} {ρ : Env} {μ μ' : Store} {e : Expr}
    {n : Int} (hσ : σ.Describes ρ) (h : Eval ρ μ e (.ok (.int n)) μ') :
    γ (aeval σ e) n := by
  induction e generalizing σ ρ μ μ' n with
  | int m => cases h; exact const_sound _
  | var x => cases h with | var hx => exact hσ x n hx
  | letin x e1 e2 ih1 ih2 =>
    cases h with
    | letin h1 h2 => exact ih2 (hσ.cons fun _ hv => by subst hv; exact ih1 hσ h1) h2
  | ite c t e _ iht ihe =>
    cases h with
    | ifT hc ht =>
      obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
      simp only [aeval, hst, Option.map_some]
      exact joinOpt_sound_l (iht hdt ht)
    | ifF hc he =>
      obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
      simp only [aeval, hse, Option.map_some]
      exact joinOpt_sound_r (ihe hde he)
  | binop op a b iha ihb =>
    generalize hr : Outcome.ok (.int n) = r at h
    cases h with
    | binop ha hb =>
      obtain ⟨x, y, rfl, rfl, hr⟩ := denote_int hr.symm
      have hx := iha hσ ha
      have hy := ihb hσ hb
      cases op <;> simp only [BinOp.denote] at hr
      case add => cases hr; exact add_sound hx hy
      case sub => cases hr; exact sub_sound hx hy
      case mul => cases hr; exact mul_sound hx hy
      case div => split at hr <;> cases hr; exact div_sound hx hy ‹_›
      case mod => split at hr <;> cases hr; exact mod_sound hx hy ‹_›
      all_goals cases hr
    | _ => cases hr
  | _ => exact top_sound _

end Diva.AbsInt
