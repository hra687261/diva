import Diva.AbsInt.Framework
import Diva.Semantics

/-!
# Abstract evaluation of integer expressions

`aeval σ e` over-approximates the integers `e` can evaluate to, in any
`NumDomain`. Only the integers are analysed, anything else gives `top`.
Conditions aren't analysed yet: both branches of an `if` are joined.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

/-- Abstract environment: what is known about the integer variables. -/
abbrev AEnv (A : Type) := List (String × A)

/-- What `σ` knows about `x` (`top` if nothing). -/
def AEnv.get [NumDomain A] (σ : AEnv A) (x : String) : A := (σ.lookup x).getD top

def aeval [NumDomain A] (σ : AEnv A) : Expr → A
  | .int n => const n
  | .var x => σ.get x
  | .binop .add a b => add (aeval σ a) (aeval σ b)
  | .binop .sub a b => sub (aeval σ a) (aeval σ b)
  | .binop .mul a b => mul (aeval σ a) (aeval σ b)
  | .binop .div a b => div (aeval σ a) (aeval σ b)
  | .binop .mod a b => mod (aeval σ a) (aeval σ b)
  | .letin x e1 e2 => aeval ((x, aeval σ e1) :: σ) e2
  | .ite _ t e => join (aeval σ t) (aeval σ e)
  | _ => top

/-- `σ` describes the integers of `ρ`. -/
def AEnv.Describes [NumDomain A] (σ : AEnv A) (ρ : Env) : Prop :=
  ∀ x n, ρ.lookup x = some (.int n) → γ (σ.get x) n

/-- If `σ` describes `ρ`, adding `x ↦ a` to `σ` and `x ↦ v` to `ρ` keeps it so,
    provided `a` describes `v` whenever `v` is an integer. -/
theorem AEnv.Describes.cons [NumDomain A] {σ : AEnv A} {ρ : Env} {x : String} {a : A}
    {v : Value} (hσ : σ.Describes ρ) (hv : ∀ k, v = .int k → γ a k) :
    AEnv.Describes ((x, a) :: σ) ((x, v) :: ρ) := by
  unfold AEnv.Describes
  intro y k hy
  by_cases hxy : x = y
  · subst hxy
    simp [List.lookup] at hy
    simpa [AEnv.get, List.lookup] using hv k hy
  · have hyx : (y == x) = false := by simp; exact Ne.symm hxy
    simp [List.lookup, hyx] at hy
    simpa [AEnv.get, List.lookup, hyx] using hσ y k hy

/-- An operator gives an integer only on integer operands. -/
theorem denote_int {op : BinOp} {va vb : Value} {n : Int}
    (h : op.denote va vb = .ok (.int n)) :
    ∃ x y, va = .int x ∧ vb = .int y ∧ op.denote (.int x) (.int y) = .ok (.int n) := by
  cases va <;> cases vb <;>
    first | exact ⟨_, _, rfl, rfl, h⟩ | (cases op <;> simp [BinOp.denote] at h)

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
    | ifT _ ht => exact join_sound_l (iht hσ ht)
    | ifF _ he => exact join_sound_r (ihe hσ he)
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
