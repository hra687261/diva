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
  | unit : Value
  | clos : Option String → String → Expr → List (String × Value) → Value
  -- `fun x -> body` with its captured env. The first field is `some f` for the
  -- recursive function `f` (from `let rec f x = body`), `none` otherwise.
  | nil  : Value
  | cons : Value → Value → Value
  deriving Repr, Inhabited

/-- Variable environment. -/
abbrev Env := List (String × Value)

/-- Denotation of a binary operator on values.
Partial: `none` for ill-typed operand combinations (e.g. `true + 1`) and for
division by zero, which therefore have no `Eval` derivation.
`Eval`'s `binop` rule is stated over this so there is one place defining what
each operator means. -/
def BinOp.denote : BinOp → Value → Value → Option Value
  | .add, .int x, .int y => some (.int (x + y))
  | .sub, .int x, .int y => some (.int (x - y))
  | .mul, .int x, .int y => some (.int (x * y))
  | .div, .int x, .int y => if y = 0 then none else some (.int (x.tdiv y))
  | .mod, .int x, .int y => if y = 0 then none else some (.int (x.tmod y))
  | .eq,  .int x, .int y => some (.bool (x == y))
  | .ne,  .int x, .int y => some (.bool (x != y))
  | .lt,  .int x, .int y => some (.bool (x < y))
  | .le,  .int x, .int y => some (.bool (x ≤ y))
  | .gt,  .int x, .int y => some (.bool (x > y))
  | .ge,  .int x, .int y => some (.bool (x ≥ y))
  | _,    _,      _      => none

/-- The call environment of a function. Calling `clos s x body ρ` on `va` extends
the env `ρ` with `x := va`.
If the function is recursive (`s = some f`), it also rebinds `f` to the closure
itself, so the body can call `f` again. -/
def callEnv (s : Option String) (x : String) (body : Expr) (ρ : Env) (va : Value) : Env :=
  match s with
  | none   => (x, va) :: ρ
  | some f => (x, va) :: (f, .clos (some f) x body ρ) :: ρ

def Value.isList : Value → Bool
  | .nil | .cons .. => true
  | _ => false

/-- Big-step operational semantics. -/
inductive Eval : Env → Expr → Value → Prop where
  | int  : Eval ρ (.int n) (.int n)
  | bool : Eval ρ (.bool b) (.bool b)
  | unit : Eval ρ .unit .unit
  | nil  : Eval ρ .nil .nil
  | var  : ρ.lookup x = some v → Eval ρ (.var x) v
  | lam  : Eval ρ (.lam x body) (.clos none x body ρ)
  | letrec {f x e1 ρ e2 v} :
    Eval ((f, .clos (some f) x e1 ρ) :: ρ) e2 v → Eval ρ (.letrec f x e1 e2) v
  | app  :
    Eval ρ f (.clos s x body ρ') → Eval ρ a va → Eval (callEnv s x body ρ' va) body v →
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
  | cons :
    Eval ρ a va → Eval ρ b vb → vb.isList = true → Eval ρ (.cons a b) (.cons va vb)
  | matchNil :
    Eval ρ s .nil → Eval ρ n v → Eval ρ (.matchList s n x xs c) v
  | matchCons :
    Eval ρ s (.cons vh vt) → Eval ((xs, vt) :: (x, vh) :: ρ) c v →
    Eval ρ (.matchList s n x xs c) v
  | assert : Eval ρ c (.bool true) → Eval ρ (.assert c) .unit

/-- Evaluation is deterministic: if e evaluates to v₁ and v₂, then v₁ = v₂. -/
theorem Eval.deterministic {ρ : Env} {e : Expr} {v₁ v₂ : Value}
    (h₁ : Eval ρ e v₁) (h₂ : Eval ρ e v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂
  case int env n => cases h₂; rfl
  case bool => cases h₂; rfl
  case unit => cases h₂; rfl
  case nil => cases h₂; rfl
  case var hlook =>
    cases h₂ with
    | var hlook2 =>
      rw [hlook] at hlook2; injection hlook2 with h
  case lam env name ebody =>
    cases h₂
    rfl
  case letrec h₂ =>
    cases h₂ with
    | letrec h2 =>
      expose_names;
      have hv1 := h₂ h2
      exact hv1
  case app ihf iha ihbody =>
    cases h₂ with
    | app hf ha hbody =>
      have hclos := ihf hf
      injection hclos with hs hx hbody' hρ'
      subst hs; subst hx; subst hbody'; subst hρ'
      have hva := iha ha
      subst hva
      exact ihbody hbody
  case letin ih1 ih2 =>
    cases h₂ with
    | letin h2a h2b =>
      expose_names;
      have hv1 := ih1 h2a
      subst hv1
      -- rw [ih2 h2b]
      exact ih2 h2b
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
  case cons iha ihb =>
    cases h₂ with
    | cons ha hb =>
      have nha := iha ha
      have nhb := ihb hb
      subst nha
      subst nhb
      rfl
  case matchNil iha ihb =>
    cases h₂ with
    | matchNil ha hb =>
      have nhb := ihb hb
      exact nhb
    | matchCons ha hb =>
      have nha := iha ha
      cases nha
  case matchCons iha ihb =>
    cases h₂ with
    | matchNil ha hb =>
      cases (iha ha)
    | matchCons ha hb =>
      have nha := iha ha
      injection nha with hh ht
      subst hh
      subst ht
      have nhb := ihb hb
      exact nhb
  case assert => cases h₂; rfl


end Diva
