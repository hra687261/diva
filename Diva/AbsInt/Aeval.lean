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

/-- **Soundness**: if `e` evaluates to the integer `n`, `aeval` describes `n`. -/
theorem aeval_sound [NumDomain A] {σ : AEnv A} {ρ : Env} {μ μ' : Store} {e : Expr}
    {n : Int} (hσ : σ.Describes ρ) (h : Eval ρ μ e (.ok (.int n)) μ') :
    γ (aeval σ e) n :=
      sorry

end Diva.AbsInt
