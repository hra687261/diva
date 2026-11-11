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

/-- Runtime errors. -/
inductive Err where
  | divZero | assertFail | typeError | unbound
  deriving Repr, DecidableEq, Inhabited

/-- The result of an evaluation: a value or a runtime error. -/
inductive Outcome where
  | ok  : Value → Outcome
  | err : Err → Outcome
  deriving Repr, Inhabited

/-- Denotation of a binary operator on values.
Ill-typed operands (e.g. `true + 1`) give `typeError`, division by zero gives
`divZero`.
`Eval`'s `binop` rule is stated over this so there is one place defining what
each operator means. -/
def BinOp.denote : BinOp → Value → Value → Outcome
  | .add, .int x, .int y => .ok (.int (x + y))
  | .sub, .int x, .int y => .ok (.int (x - y))
  | .mul, .int x, .int y => .ok (.int (x * y))
  | .div, .int x, .int y => if y = 0 then .err .divZero else .ok (.int (x.tdiv y))
  | .mod, .int x, .int y => if y = 0 then .err .divZero else .ok (.int (x.tmod y))
  | .eq,  .int x, .int y => .ok (.bool (x == y))
  | .ne,  .int x, .int y => .ok (.bool (x != y))
  | .lt,  .int x, .int y => .ok (.bool (x < y))
  | .le,  .int x, .int y => .ok (.bool (x ≤ y))
  | .gt,  .int x, .int y => .ok (.bool (x > y))
  | .ge,  .int x, .int y => .ok (.bool (x ≥ y))
  | .eq,  .bool x, .bool y => .ok (.bool (x == y))
  | .ne,  .bool x, .bool y => .ok (.bool (x != y))
  | .eq,  .unit, .unit   => .ok (.bool true)
  | .ne,  .unit, .unit   => .ok (.bool false)
  | _,    _,      _      => .err .typeError

/-- The call environment of a function. Calling `clos s x body ρ` on `va` extends
the env `ρ` with `x := va`.
If the function is recursive (`s = some f`), it also rebinds `f` to the closure
itself, so the body can call `f` again. -/
def callEnv (s : Option String) (x : String) (body : Expr) (ρ : Env) (va : Value) : Env :=
  match s with
  | none   => (x, va) :: ρ
  | some f => (x, va) :: (f, .clos (some f) x body ρ) :: ρ

def Value.isClos : Value → Bool
  | .clos .. => true
  | _ => false

def Value.isBool : Value → Bool
  | .bool _ => true
  | _ => false

def Value.isList : Value → Bool
  | .nil | .cons .. => true
  | _ => false

/-- Big-step operational semantics. Besides its normal rules, each construct has
one rule per way it can fail on a value of the wrong kind, and one rule per
sub-expression whose error it propagates (left to right). -/
inductive Eval : Env → Expr → Outcome → Prop where
  | int  : Eval ρ (.int n) (.ok (.int n))
  | bool : Eval ρ (.bool b) (.ok (.bool b))
  | unit : Eval ρ .unit (.ok .unit)
  | nil  : Eval ρ .nil (.ok .nil)
  | var  : ρ.lookup x = some v → Eval ρ (.var x) (.ok v)
  | varErr : ρ.lookup x = none → Eval ρ (.var x) (.err .unbound)
  | lam  : Eval ρ (.lam x body) (.ok (.clos none x body ρ))
  | letrec {f x e1 ρ e2 r} :
    Eval ((f, .clos (some f) x e1 ρ) :: ρ) e2 r → Eval ρ (.letrec f x e1 e2) r
  | app  :
    Eval ρ f (.ok (.clos s x body ρ')) → Eval ρ a (.ok va) →
    Eval (callEnv s x body ρ' va) body r →
    Eval ρ (.app f a) r
  | appNotFn :
    Eval ρ f (.ok vf) → vf.isClos = false → Eval ρ a (.ok va) →
    Eval ρ (.app f a) (.err .typeError)
  | appErrF : Eval ρ f (.err k) → Eval ρ (.app f a) (.err k)
  | appErrA : Eval ρ f (.ok vf) → Eval ρ a (.err k) → Eval ρ (.app f a) (.err k)
  | letin :
    Eval ρ e1 (.ok v1) → Eval ((x, v1) :: ρ) e2 r → Eval ρ (.letin x e1 e2) r
  | letinErr : Eval ρ e1 (.err k) → Eval ρ (.letin x e1 e2) (.err k)
  | ifT  :
    Eval ρ c (.ok (.bool true)) → Eval ρ t r → Eval ρ (.ite c t e) r
  | ifF  :
    Eval ρ c (.ok (.bool false)) → Eval ρ e r → Eval ρ (.ite c t e) r
  | ifNotBool :
    Eval ρ c (.ok v) → v.isBool = false → Eval ρ (.ite c t e) (.err .typeError)
  | ifErr : Eval ρ c (.err k) → Eval ρ (.ite c t e) (.err k)
  | binop :
    Eval ρ a (.ok va) → Eval ρ b (.ok vb) →
    Eval ρ (.binop op a b) (op.denote va vb)
  | binopErrL : Eval ρ a (.err k) → Eval ρ (.binop op a b) (.err k)
  | binopErrR :
    Eval ρ a (.ok va) → Eval ρ b (.err k) → Eval ρ (.binop op a b) (.err k)
  | cons :
    Eval ρ a (.ok va) → Eval ρ b (.ok vb) → vb.isList = true →
    Eval ρ (.cons a b) (.ok (.cons va vb))
  | consNotList :
    Eval ρ a (.ok va) → Eval ρ b (.ok vb) → vb.isList = false →
    Eval ρ (.cons a b) (.err .typeError)
  | consErrL : Eval ρ a (.err k) → Eval ρ (.cons a b) (.err k)
  | consErrR :
    Eval ρ a (.ok va) → Eval ρ b (.err k) → Eval ρ (.cons a b) (.err k)
  | matchNil :
    Eval ρ s (.ok .nil) → Eval ρ n r → Eval ρ (.matchList s n x xs c) r
  | matchCons :
    Eval ρ s (.ok (.cons vh vt)) → Eval ((xs, vt) :: (x, vh) :: ρ) c r →
    Eval ρ (.matchList s n x xs c) r
  | matchNotList :
    Eval ρ s (.ok v) → v.isList = false →
    Eval ρ (.matchList s n x xs c) (.err .typeError)
  | matchErr : Eval ρ s (.err k) → Eval ρ (.matchList s n x xs c) (.err k)
  | assert : Eval ρ c (.ok (.bool true)) → Eval ρ (.assert c) (.ok .unit)
  | assertF : Eval ρ c (.ok (.bool false)) → Eval ρ (.assert c) (.err .assertFail)
  | assertNotBool :
    Eval ρ c (.ok v) → v.isBool = false → Eval ρ (.assert c) (.err .typeError)
  | assertErr : Eval ρ c (.err k) → Eval ρ (.assert c) (.err k)

/-- Evaluation is deterministic: if e evaluates to r₁ and r₂, then r₁ = r₂. -/
theorem Eval.deterministic {ρ : Env} {e : Expr} {r₁ r₂ : Outcome}
    (h₁ : Eval ρ e r₁) (h₂ : Eval ρ e r₂) : r₁ = r₂ := by
  induction h₁ generalizing r₂
  case int env n => cases h₂; rfl
  case bool => cases h₂; rfl
  case unit => cases h₂; rfl
  case nil => cases h₂; rfl
  case var h =>
    cases h₂
    case var hl2 =>
      rw [h] at hl2
      injection hl2 with val_eq
      subst val_eq
      rfl
    case varErr hl2 => rw [h] at hl2; cases hl2
  case varErr h =>
    cases h₂
    case var hl2 => rw [h] at hl2; cases hl2
    case varErr hl2 => rfl
  case lam env name ebody => cases h₂; rfl
  case letrec h₂ =>
    cases h₂ with
    | letrec h2 => exact h₂ h2
  case app ihf iha ihb =>
    cases h₂ with
    | app hf ha hb => cases ihf hf; cases iha ha; exact ihb hb
    | appNotFn hf hnc _ => cases ihf hf; cases hnc
    | appErrF hf => cases ihf hf
    | appErrA _ ha => cases iha ha
  case appNotFn hnc _ ihf iha =>
    cases h₂ with
    | app hf _ _ => cases ihf hf; cases hnc
    | appNotFn => rfl
    | appErrF hf => cases ihf hf
    | appErrA _ ha => cases iha ha
  case appErrF ihf =>
    cases h₂ with
    | app hf _ _ => cases ihf hf
    | appNotFn hf _ _ => cases ihf hf
    | appErrF hf => cases ihf hf; rfl
    | appErrA hf _ => cases ihf hf
  case appErrA ihf iha =>
    cases h₂ with
    | app _ ha _ => cases iha ha
    | appNotFn _ _ ha => cases iha ha
    | appErrF hf => cases ihf hf
    | appErrA _ ha => cases iha ha; rfl
  case letin ih1 ih2 =>
    cases h₂ with
    | letin h1 h2 => cases ih1 h1; exact ih2 h2
    | letinErr h1 => cases ih1 h1
  case letinErr ih1 =>
    cases h₂ with
    | letin h1 _ => cases ih1 h1
    | letinErr h1 => cases ih1 h1; rfl
  case ifT ihc iht =>
    cases h₂ with
    | ifT _ ht => exact iht ht
    | ifF hc _ => cases ihc hc
    | ifNotBool hc hnb => cases ihc hc; cases hnb
    | ifErr hc => cases ihc hc
  case ifF ihc ihe =>
    cases h₂ with
    | ifT hc _ => cases ihc hc
    | ifF _ he => exact ihe he
    | ifNotBool hc hnb => cases ihc hc; cases hnb
    | ifErr hc => cases ihc hc
  case ifNotBool hnb ihc =>
    cases h₂ with
    | ifT hc _ => cases ihc hc; cases hnb
    | ifF hc _ => cases ihc hc; cases hnb
    | ifNotBool => rfl
    | ifErr hc => cases ihc hc
  case ifErr ihc =>
    cases h₂ with
    | ifT hc _ => cases ihc hc
    | ifF hc _ => cases ihc hc
    | ifNotBool hc _ => cases ihc hc
    | ifErr hc => cases ihc hc; rfl
  case binop iha ihb =>
    cases h₂ with
    | binop ha hb => cases iha ha; cases ihb hb; rfl
    | binopErrL ha => cases iha ha
    | binopErrR _ hb => cases ihb hb
  case binopErrL iha =>
    cases h₂ with
    | binop ha _ => cases iha ha
    | binopErrL ha => cases iha ha; rfl
    | binopErrR ha _ => cases iha ha
  case binopErrR iha ihb =>
    cases h₂ with
    | binop _ hb => cases ihb hb
    | binopErrL ha => cases iha ha
    | binopErrR _ hb => cases ihb hb; rfl
  case cons hl iha ihb =>
    cases h₂ with
    | cons ha hb _ => cases iha ha; cases ihb hb; rfl
    | consNotList ha hb hl' => cases iha ha; cases ihb hb; rw [hl] at hl'; cases hl'
    | consErrL ha => cases iha ha
    | consErrR _ hb => cases ihb hb
  case consNotList hl iha ihb =>
    cases h₂ with
    | cons ha hb hl' => cases iha ha; cases ihb hb; rw [hl] at hl'; cases hl'
    | consNotList => rfl
    | consErrL ha => cases iha ha
    | consErrR _ hb => cases ihb hb
  case consErrL iha =>
    cases h₂ with
    | cons ha _ _ => cases iha ha
    | consNotList ha _ _ => cases iha ha
    | consErrL ha => cases iha ha; rfl
    | consErrR ha _ => cases iha ha
  case consErrR iha ihb =>
    cases h₂ with
    | cons _ hb _ => cases ihb hb
    | consNotList _ hb _ => cases ihb hb
    | consErrL ha => cases iha ha
    | consErrR _ hb => cases ihb hb; rfl
  case matchNil ihs ihn =>
    cases h₂ with
    | matchNil _ hn => exact ihn hn
    | matchCons hs _ => cases ihs hs
    | matchNotList hs hnl => cases ihs hs; cases hnl
    | matchErr hs => cases ihs hs
  case matchCons ihs ihc =>
    cases h₂ with
    | matchNil hs _ => cases ihs hs
    | matchCons hs hc => cases ihs hs; exact ihc hc
    | matchNotList hs hnl => cases ihs hs; cases hnl
    | matchErr hs => cases ihs hs
  case matchNotList hnl ihs =>
    cases h₂ with
    | matchNil hs _ => cases ihs hs; cases hnl
    | matchCons hs _ => cases ihs hs; cases hnl
    | matchNotList => rfl
    | matchErr hs => cases ihs hs
  case matchErr ihs =>
    cases h₂ with
    | matchNil hs _ => cases ihs hs
    | matchCons hs _ => cases ihs hs
    | matchNotList hs _ => cases ihs hs
    | matchErr hs => cases ihs hs; rfl
  case assert ihc =>
    cases h₂ with
    | assert => rfl
    | assertF hc => cases ihc hc
    | assertNotBool hc hnb => cases ihc hc; cases hnb
    | assertErr hc => cases ihc hc
  case assertF ihc =>
    cases h₂ with
    | assert hc => cases ihc hc
    | assertF => rfl
    | assertNotBool hc hnb => cases ihc hc; cases hnb
    | assertErr hc => cases ihc hc
  case assertNotBool hnb ihc =>
    cases h₂ with
    | assert hc => cases ihc hc; cases hnb
    | assertF hc => cases ihc hc; cases hnb
    | assertNotBool => rfl
    | assertErr hc => cases ihc hc
  case assertErr ihc =>
    cases h₂ with
    | assert hc => cases ihc hc
    | assertF hc => cases ihc hc
    | assertNotBool hc _ => cases ihc hc
    | assertErr hc => cases ihc hc; rfl

end Diva
