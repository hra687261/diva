import Diva.Ast

/-!
# Operational semantics (ground truth)

The big-step relation `Eval` is the meaning of the IR. Everything else is proved
correct against it, so `Eval` (plus the Lean kernel) is the entire trusted base.

TODO:
* add a mutable store for refs/arrays
-/

namespace Diva

/-- Runtime values. -/
inductive Value where
  | int  : Int → Value
  | bool : Bool → Value
  | clos : String → Expr → List (String × Value) → Value  -- `fun x -> body` + captured env
  deriving Repr, Inhabited

/-- Variable environment. -/
abbrev Env := List (String × Value)

/-- Denotation of a binary operator on values.
Partial: `none` for ill-typed operand combinations (e.g. `true + 1`), which
therefore have no `Eval` derivation.
`Eval`'s `binop` rule is stated over this so there is one place defining what
each operator means. -/
def BinOp.denote : BinOp → Value → Value → Option Value
  | .add, .int x, .int y => some (.int (x + y))
  | .sub, .int x, .int y => some (.int (x - y))
  | .mul, .int x, .int y => some (.int (x * y))
  | .eq,  .int x, .int y => some (.bool (x == y))
  | .lt,  .int x, .int y => some (.bool (decide (x < y)))
  | _,    _,      _      => none

/-- Big-step operational semantics. -/
inductive Eval : Env → Expr → Value → Prop where
  | int  : Eval ρ (.int n) (.int n)
  | bool : Eval ρ (.bool b) (.bool b)
  | var  : ρ.lookup x = some v → Eval ρ (.var x) v
  | lam  : Eval ρ (.lam x body) (.clos x body ρ)
  | app  :
    Eval ρ f (.clos x body ρ') → Eval ρ a va → Eval ((x, va) :: ρ') body v →
    Eval ρ (.app f a) v
  | letin :
    Eval ρ e1 v1 → Eval ((x, v1) :: ρ) e2 v → Eval ρ (.letin x e1 e2) v
  | ifT  :
    Eval ρ c (.bool true) → Eval ρ t v → Eval ρ (.ite c t e) v
  | ifF  :
    Eval ρ c (.bool false) → Eval ρ e v → Eval ρ (.ite c t e) v
  | binop :
    Eval ρ a va → Eval ρ b vb →
    BinOp.denote op va vb = some v →
    Eval ρ (.binop op a b) v

/-- Evaluation is deterministic: if e evaluates to v₁ and v₂, then v₁ = v₂. -/
theorem Eval.deterministic {ρ : Env} {e : Expr} {v₁ v₂ : Value}
    (h₁ : Eval ρ e v₁) (h₂ : Eval ρ e v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂
  case int env n => cases h₂; rfl
  case bool => cases h₂; rfl
  case var hlook =>
    cases h₂ with
    | var hlook2 =>
      rw [hlook] at hlook2; injection hlook2 with h
  case letin ih1 ih2 =>
    cases h₂ with
    | letin h2a h2b =>
      expose_names;
      have hv1 := ih1 h2a
      subst hv1
      -- rw [ih2 h2b]
      exact ih2 h2b
  case lam env name ebody =>
    cases h₂
    rfl
  case app ihf iha ihbody =>
    cases h₂ with
    | app hf ha hbody =>
      have hclos := ihf hf
      injection hclos with hx hbody' hρ'
      subst hx; subst hbody'; subst hρ'
      have hva := iha ha
      subst hva
      exact ihbody hbody
  -- case ifT =>
  --   cases h₂ with
  --   | ifT =>
  --     expose_names;
  --     rw [a_ih_1 h_3]
  --   | ifF =>
  --     expose_names;
  --     have contra := a_ih h_2
  --     simp at contra
  -- case ifF =>
  --   cases h₂ with
  --   | ifT =>
  --     expose_names;
  --     have contra := a_ih h_2
  --     simp at contra
  --   | ifF =>
  --     expose_names;
  --     rw [a_ih_1 h_3]
  case ifT ihc ihbr | ifF ihc ihbr =>
    cases h₂ <;>
      first
      | (rename_i _ hbr; rw [ihbr hbr])
        -- or: exact ihbr hbr
      | (rename_i hc _; have c := ihc hc; simp at c)
  case binop =>
    cases h₂ with
    | binop =>
      expose_names;
      have hclos1 := a_ih h_3
      have hclos2 := a_ih_1 h_4
      subst hclos1
      subst hclos2
      rw [h_2] at h_5
      injection h_5

end Diva
