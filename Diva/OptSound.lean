import Diva.Opt
import Diva.AbsInt.MayFail

/-!
# Correctness of the optimiser

A program and its optimised version give related outcomes and related stores.
Related values are equal, except closures: the optimised closure's body is the
optimised body (`opt` rewrites under `fun`), so the relation is not equality.

The optimiser adds and removes no allocation, so addresses stay the same.

Status: statement only, the proof is `sorry`. It would go by induction on `Eval`,
in both directions. An expression that is replaced by its value is inert: it
terminates and leaves the store unchanged.
-/

namespace Diva.Opt

open AbsInt

variable {A : Type} [NumDomain A]

/-- A source value and an optimised value that agree. -/
inductive VR (H : Hints A) : Value → Value → Prop where
  | int {n : Int} : VR H (.int n) (.int n)
  | bool {b : Bool} : VR H (.bool b) (.bool b)
  | unit : VR H .unit .unit
  | nil : VR H .nil .nil
  | cons {a a' b b' : Value} : VR H a a' → VR H b b' → VR H (.cons a b) (.cons a' b')
  | arr {l : Nat} : VR H (.arr l) (.arr l)
  | ref {l : Nat} : VR H (.ref l) (.ref l)
  | exn {t : String} {a a' : Value} : VR H a a' → VR H (.exn t a) (.exn t a')
  -- the optimised closure has the optimised body, and a related environment
  | clos {s : Option String} {x : String} {b : Expr} {ρ ρ' : Env} (σ : AEnv A) :
      (∀ y w w', ρ.lookup y = some w → ρ'.lookup y = some w' → VR H w w') →
      (∀ y, (ρ.lookup y).isSome = (ρ'.lookup y).isSome) →
      σ.Describes ρ →
      VR H (.clos s x b ρ) (.clos s x (opt H (bodyEnv H σ s x b) b) ρ')

/-- Related outcomes: related values, related raised exceptions, or the same runtime
    error. -/
def OutRel (H : Hints A) : Outcome → Outcome → Prop
  | .ok v, .ok v' => VR H v v'
  | .err (.exn v), .err (.exn v') => VR H v v'
  | .err k, .err k' => k = k'
  | _, _ => False

/-- Related stores: the same addresses, with related contents. -/
def StoreRel (H : Hints A) (μ μ' : Store) : Prop :=
  μ.length = μ'.length ∧
  ∀ (l : Nat) (c c' : List Value), μ[l]? = some c → μ'[l]? = some c' →
    c.length = c'.length ∧ ∀ (i : Nat) v v', c[i]? = some v → c'[i]? = some v' → VR H v v'

/-- Two programs without free variables are equivalent: each gives an outcome iff
    the other does, and the outcomes and final stores are related. -/
def Equiv (H : Hints A) (e e' : Expr) : Prop :=
  (∀ r μ, Eval [] [] e r μ → ∃ r' μ', Eval [] [] e' r' μ' ∧ OutRel H r r' ∧ StoreRel H μ μ') ∧
  (∀ r' μ', Eval [] [] e' r' μ' → ∃ r μ, Eval [] [] e r μ ∧ OutRel H r r' ∧ StoreRel H μ μ')

/-- On integers, related means equal. -/
theorem VR.int_eq {H : Hints A} {n : Int} {v : Value} (h : VR H (.int n) v) :
    v = .int n := by
  cases h
  rfl

/-- **The optimiser preserves the meaning of programs.** -/
theorem optimize_correct (e : Expr) :
    Equiv (inferHints ([] : AEnv A) e) e (optimize ([] : AEnv A) e) := by
  sorry

end Diva.Opt
