import Diva.Ast

/-!
# Operational semantics (ground truth)

The big-step relation `Eval` is the meaning of the IR. Everything else is proved
correct against it, so `Eval` (plus the Lean kernel) is the entire trusted base.
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
  | arr  : Nat → Value  -- the address of an array in the store
  | ref  : Nat → Value  -- the address of a ref in the store
  | exn  : String → Value → Value  -- the exception `E v`
  deriving Repr, Inhabited

/-- Variable environment. -/
abbrev Env := List (String × Value)

/-- The store: the contents of the arrays and refs, by address (a ref holds one
value). An array's length never changes. -/
abbrev Store := List (List Value)

/-- Runtime errors, and raised exceptions (`exn v`). -/
inductive Err where
  | divZero | assertFail | typeError | unbound | outOfBounds
  | exn : Value → Err
  deriving Repr, Inhabited

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

/-! ## Store operations on values (like `BinOp.denote`) -/

/-- `Array.make n v`: a new array of `n` copies of `v`, at the next address. -/
def allocV (μ : Store) : Value → Value → Outcome × Store
  | .int n, v =>
    if n < 0 then (.err .outOfBounds, μ)
    else (.ok (.arr μ.length), μ ++ [List.replicate n.toNat v])
  | _, _ => (.err .typeError, μ)

/-- `a.(i)`. -/
def getV (μ : Store) : Value → Value → Outcome
  | .arr l, .int i =>
    match μ[l]? with
    | some arr => if 0 ≤ i ∧ i < arr.length then .ok arr[i.toNat]! else .err .outOfBounds
    | none => .err .outOfBounds
  | _, _ => .err .typeError

/-- `a.(i) <- v`. -/
def setV (μ : Store) : Value → Value → Value → Outcome × Store
  | .arr l, .int i, v =>
    match μ[l]? with
    | some arr =>
      if 0 ≤ i ∧ i < arr.length then (.ok .unit, μ.set l (arr.set i.toNat v))
      else (.err .outOfBounds, μ)
    | none => (.err .outOfBounds, μ)
  | _, _, _ => (.err .typeError, μ)

/-- `Array.length a`. -/
def lenV (μ : Store) : Value → Outcome
  | .arr l =>
    match μ[l]? with
    | some arr => .ok (.int arr.length)
    | none => .err .outOfBounds
  | _ => .err .typeError

/-- `ref v`: a new ref holding `v`, at the next address. -/
def refV (μ : Store) (v : Value) : Outcome × Store := (.ok (.ref μ.length), μ ++ [[v]])

/-- `!r`. -/
def derefV (μ : Store) : Value → Outcome
  | .ref l =>
    match μ[l]? with
    | some (v :: _) => .ok v
    | _ => .err .outOfBounds
  | _ => .err .typeError

/-- `r := v`. -/
def assignV (μ : Store) : Value → Value → Outcome × Store
  | .ref l, v =>
    match μ[l]? with
    | some _ => (.ok .unit, μ.set l [v])
    | none => (.err .outOfBounds, μ)
  | _, _ => (.err .typeError, μ)

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

def Value.isExn : Value → Bool
  | .exn .. => true
  | _ => false

/-- Big-step semantics: `Eval ρ μ e r μ'` means `e`, run in `ρ` from store `μ`,
gives `r` and store `μ'`. Evaluation is left to right; errors propagate. -/
inductive Eval : Env → Store → Expr → Outcome → Store → Prop where
  | int  : Eval ρ μ (.int n) (.ok (.int n)) μ
  | bool : Eval ρ μ (.bool b) (.ok (.bool b)) μ
  | unit : Eval ρ μ .unit (.ok .unit) μ
  | nil  : Eval ρ μ .nil (.ok .nil) μ
  | var  : ρ.lookup x = some v → Eval ρ μ (.var x) (.ok v) μ
  | varErr : ρ.lookup x = none → Eval ρ μ (.var x) (.err .unbound) μ
  | lam  : Eval ρ μ (.lam x body) (.ok (.clos none x body ρ)) μ
  | letrec {f x e1 ρ μ e2 r μ'} :
    Eval ((f, .clos (some f) x e1 ρ) :: ρ) μ e2 r μ' → Eval ρ μ (.letrec f x e1 e2) r μ'
  | app  :
    Eval ρ μ f (.ok (.clos s x body ρ')) μ₁ → Eval ρ μ₁ a (.ok va) μ₂ →
    Eval (callEnv s x body ρ' va) μ₂ body r μ₃ →
    Eval ρ μ (.app f a) r μ₃
  | appNotFn :
    Eval ρ μ f (.ok vf) μ₁ → vf.isClos = false → Eval ρ μ₁ a (.ok va) μ₂ →
    Eval ρ μ (.app f a) (.err .typeError) μ₂
  | appErrF : Eval ρ μ f (.err k) μ₁ → Eval ρ μ (.app f a) (.err k) μ₁
  | appErrA :
    Eval ρ μ f (.ok vf) μ₁ → Eval ρ μ₁ a (.err k) μ₂ → Eval ρ μ (.app f a) (.err k) μ₂
  | letin :
    Eval ρ μ e1 (.ok v1) μ₁ → Eval ((x, v1) :: ρ) μ₁ e2 r μ₂ →
    Eval ρ μ (.letin x e1 e2) r μ₂
  | letinErr : Eval ρ μ e1 (.err k) μ₁ → Eval ρ μ (.letin x e1 e2) (.err k) μ₁
  | ifT  :
    Eval ρ μ c (.ok (.bool true)) μ₁ → Eval ρ μ₁ t r μ₂ → Eval ρ μ (.ite c t e) r μ₂
  | ifF  :
    Eval ρ μ c (.ok (.bool false)) μ₁ → Eval ρ μ₁ e r μ₂ → Eval ρ μ (.ite c t e) r μ₂
  | ifNotBool :
    Eval ρ μ c (.ok v) μ₁ → v.isBool = false →
    Eval ρ μ (.ite c t e) (.err .typeError) μ₁
  | ifErr : Eval ρ μ c (.err k) μ₁ → Eval ρ μ (.ite c t e) (.err k) μ₁
  | binop :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ b (.ok vb) μ₂ →
    Eval ρ μ (.binop op a b) (op.denote va vb) μ₂
  | binopErrL : Eval ρ μ a (.err k) μ₁ → Eval ρ μ (.binop op a b) (.err k) μ₁
  | binopErrR :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ b (.err k) μ₂ →
    Eval ρ μ (.binop op a b) (.err k) μ₂
  | cons :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ b (.ok vb) μ₂ → vb.isList = true →
    Eval ρ μ (.cons a b) (.ok (.cons va vb)) μ₂
  | consNotList :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ b (.ok vb) μ₂ → vb.isList = false →
    Eval ρ μ (.cons a b) (.err .typeError) μ₂
  | consErrL : Eval ρ μ a (.err k) μ₁ → Eval ρ μ (.cons a b) (.err k) μ₁
  | consErrR :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ b (.err k) μ₂ → Eval ρ μ (.cons a b) (.err k) μ₂
  | matchNil :
    Eval ρ μ s (.ok .nil) μ₁ → Eval ρ μ₁ n r μ₂ → Eval ρ μ (.matchList s n x xs c) r μ₂
  | matchCons :
    Eval ρ μ s (.ok (.cons vh vt)) μ₁ → Eval ((xs, vt) :: (x, vh) :: ρ) μ₁ c r μ₂ →
    Eval ρ μ (.matchList s n x xs c) r μ₂
  | matchNotList :
    Eval ρ μ s (.ok v) μ₁ → v.isList = false →
    Eval ρ μ (.matchList s n x xs c) (.err .typeError) μ₁
  | matchErr :
    Eval ρ μ s (.err k) μ₁ → Eval ρ μ (.matchList s n x xs c) (.err k) μ₁
  | assert : Eval ρ μ c (.ok (.bool true)) μ₁ → Eval ρ μ (.assert c) (.ok .unit) μ₁
  | assertF :
    Eval ρ μ c (.ok (.bool false)) μ₁ → Eval ρ μ (.assert c) (.err .assertFail) μ₁
  | assertNotBool :
    Eval ρ μ c (.ok v) μ₁ → v.isBool = false →
    Eval ρ μ (.assert c) (.err .typeError) μ₁
  | assertErr : Eval ρ μ c (.err k) μ₁ → Eval ρ μ (.assert c) (.err k) μ₁
  | alloc :
    Eval ρ μ n (.ok vn) μ₁ → Eval ρ μ₁ v (.ok vv) μ₂ →
    Eval ρ μ (.alloc site n v) (allocV μ₂ vn vv).1 (allocV μ₂ vn vv).2
  | allocErrN : Eval ρ μ n (.err k) μ₁ → Eval ρ μ (.alloc site n v) (.err k) μ₁
  | allocErrV :
    Eval ρ μ n (.ok vn) μ₁ → Eval ρ μ₁ v (.err k) μ₂ →
    Eval ρ μ (.alloc site n v) (.err k) μ₂
  | get :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ i (.ok vi) μ₂ →
    Eval ρ μ (.get a i) (getV μ₂ va vi) μ₂
  | getErrA : Eval ρ μ a (.err k) μ₁ → Eval ρ μ (.get a i) (.err k) μ₁
  | getErrI :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ i (.err k) μ₂ → Eval ρ μ (.get a i) (.err k) μ₂
  | set :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ i (.ok vi) μ₂ → Eval ρ μ₂ v (.ok vv) μ₃ →
    Eval ρ μ (.set a i v) (setV μ₃ va vi vv).1 (setV μ₃ va vi vv).2
  | setErrA : Eval ρ μ a (.err k) μ₁ → Eval ρ μ (.set a i v) (.err k) μ₁
  | setErrI :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ i (.err k) μ₂ → Eval ρ μ (.set a i v) (.err k) μ₂
  | setErrV :
    Eval ρ μ a (.ok va) μ₁ → Eval ρ μ₁ i (.ok vi) μ₂ → Eval ρ μ₂ v (.err k) μ₃ →
    Eval ρ μ (.set a i v) (.err k) μ₃
  | len : Eval ρ μ a (.ok va) μ₁ → Eval ρ μ (.len a) (lenV μ₁ va) μ₁
  | lenErr : Eval ρ μ a (.err k) μ₁ → Eval ρ μ (.len a) (.err k) μ₁
  | ref :
    Eval ρ μ e (.ok v) μ₁ → Eval ρ μ (.ref site e) (refV μ₁ v).1 (refV μ₁ v).2
  | refErr : Eval ρ μ e (.err k) μ₁ → Eval ρ μ (.ref site e) (.err k) μ₁
  | deref : Eval ρ μ r (.ok vr) μ₁ → Eval ρ μ (.deref r) (derefV μ₁ vr) μ₁
  | derefErr : Eval ρ μ r (.err k) μ₁ → Eval ρ μ (.deref r) (.err k) μ₁
  | assign :
    Eval ρ μ r (.ok vr) μ₁ → Eval ρ μ₁ e (.ok v) μ₂ →
    Eval ρ μ (.assign r e) (assignV μ₂ vr v).1 (assignV μ₂ vr v).2
  | assignErrR : Eval ρ μ r (.err k) μ₁ → Eval ρ μ (.assign r e) (.err k) μ₁
  | assignErrV :
    Eval ρ μ r (.ok vr) μ₁ → Eval ρ μ₁ e (.err k) μ₂ → Eval ρ μ (.assign r e) (.err k) μ₂
  | exn : Eval ρ μ e (.ok v) μ₁ → Eval ρ μ (.exn c e) (.ok (.exn c v)) μ₁
  | exnErr : Eval ρ μ e (.err k) μ₁ → Eval ρ μ (.exn c e) (.err k) μ₁
  | raise :
    Eval ρ μ e (.ok v) μ₁ → v.isExn = true → Eval ρ μ (.raise e) (.err (.exn v)) μ₁
  | raiseNotExn :
    Eval ρ μ e (.ok v) μ₁ → v.isExn = false → Eval ρ μ (.raise e) (.err .typeError) μ₁
  | raiseErr : Eval ρ μ e (.err k) μ₁ → Eval ρ μ (.raise e) (.err k) μ₁

/-- Evaluation is deterministic: the same expression, environment and store give
the same outcome and the same final store. -/
theorem Eval.deterministic {ρ : Env} {μ : Store} {e : Expr} {r₁ r₂ : Outcome}
    {μ₁ μ₂ : Store} (h₁ : Eval ρ μ e r₁ μ₁) (h₂ : Eval ρ μ e r₂ μ₂) :
    (r₁, μ₁) = (r₂, μ₂) := by
  induction h₁ generalizing r₂ μ₂
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
    | appErrA hf ha => cases ihf hf; cases iha ha
  case appNotFn hnc _ ihf iha =>
    cases h₂ with
    | app hf _ _ => cases ihf hf; cases hnc
    | appNotFn hf _ ha => cases ihf hf; cases iha ha; rfl
    | appErrF hf => cases ihf hf
    | appErrA hf ha => cases ihf hf; cases iha ha
  case appErrF ihf =>
    cases h₂ with
    | app hf _ _ => cases ihf hf
    | appNotFn hf _ _ => cases ihf hf
    | appErrF hf => cases ihf hf; rfl
    | appErrA hf _ => cases ihf hf
  case appErrA ihf iha =>
    cases h₂ with
    | app hf ha _ => cases ihf hf; cases iha ha
    | appNotFn hf _ ha => cases ihf hf; cases iha ha
    | appErrF hf => cases ihf hf
    | appErrA hf ha => cases ihf hf; cases iha ha; rfl
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
    | ifT hc ht => cases ihc hc; exact iht ht
    | ifF hc _ => cases ihc hc
    | ifNotBool hc hnb => cases ihc hc; cases hnb
    | ifErr hc => cases ihc hc
  case ifF ihc ihe =>
    cases h₂ with
    | ifT hc _ => cases ihc hc
    | ifF hc he => cases ihc hc; exact ihe he
    | ifNotBool hc hnb => cases ihc hc; cases hnb
    | ifErr hc => cases ihc hc
  case ifNotBool hnb ihc =>
    cases h₂ with
    | ifT hc _ => cases ihc hc; cases hnb
    | ifF hc _ => cases ihc hc; cases hnb
    | ifNotBool hc _ => cases ihc hc; rfl
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
    | binopErrR ha hb => cases iha ha; cases ihb hb
  case binopErrL iha =>
    cases h₂ with
    | binop ha _ => cases iha ha
    | binopErrL ha => cases iha ha; rfl
    | binopErrR ha _ => cases iha ha
  case binopErrR iha ihb =>
    cases h₂ with
    | binop ha hb => cases iha ha; cases ihb hb
    | binopErrL ha => cases iha ha
    | binopErrR ha hb => cases iha ha; cases ihb hb; rfl
  case cons hl iha ihb =>
    cases h₂ with
    | cons ha hb _ => cases iha ha; cases ihb hb; rfl
    | consNotList ha hb hl' => cases iha ha; cases ihb hb; rw [hl] at hl'; cases hl'
    | consErrL ha => cases iha ha
    | consErrR ha hb => cases iha ha; cases ihb hb
  case consNotList hl iha ihb =>
    cases h₂ with
    | cons ha hb hl' => cases iha ha; cases ihb hb; rw [hl] at hl'; cases hl'
    | consNotList ha hb _ => cases iha ha; cases ihb hb; rfl
    | consErrL ha => cases iha ha
    | consErrR ha hb => cases iha ha; cases ihb hb
  case consErrL iha =>
    cases h₂ with
    | cons ha _ _ => cases iha ha
    | consNotList ha _ _ => cases iha ha
    | consErrL ha => cases iha ha; rfl
    | consErrR ha _ => cases iha ha
  case consErrR iha ihb =>
    cases h₂ with
    | cons ha hb _ => cases iha ha; cases ihb hb
    | consNotList ha hb _ => cases iha ha; cases ihb hb
    | consErrL ha => cases iha ha
    | consErrR ha hb => cases iha ha; cases ihb hb; rfl
  case matchNil ihs ihn =>
    cases h₂ with
    | matchNil hs hn => cases ihs hs; exact ihn hn
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
    | matchNotList hs _ => cases ihs hs; rfl
    | matchErr hs => cases ihs hs
  case matchErr ihs =>
    cases h₂ with
    | matchNil hs _ => cases ihs hs
    | matchCons hs _ => cases ihs hs
    | matchNotList hs _ => cases ihs hs
    | matchErr hs => cases ihs hs; rfl
  case assert ihc =>
    cases h₂ with
    | assert hc => cases ihc hc; rfl
    | assertF hc => cases ihc hc
    | assertNotBool hc hnb => cases ihc hc; cases hnb
    | assertErr hc => cases ihc hc
  case assertF ihc =>
    cases h₂ with
    | assert hc => cases ihc hc
    | assertF hc => cases ihc hc; rfl
    | assertNotBool hc hnb => cases ihc hc; cases hnb
    | assertErr hc => cases ihc hc
  case assertNotBool hnb ihc =>
    cases h₂ with
    | assert hc => cases ihc hc; cases hnb
    | assertF hc => cases ihc hc; cases hnb
    | assertNotBool hc _ => cases ihc hc; rfl
    | assertErr hc => cases ihc hc
  case assertErr ihc =>
    cases h₂ with
    | assert hc => cases ihc hc
    | assertF hc => cases ihc hc
    | assertNotBool hc _ => cases ihc hc
    | assertErr hc => cases ihc hc; rfl
  case alloc ihn ihv =>
    cases h₂ with
    | alloc hn hv => cases ihn hn; cases ihv hv; rfl
    | allocErrN hn => cases ihn hn
    | allocErrV hn hv => cases ihn hn; cases ihv hv
  case allocErrN ihn =>
    cases h₂ with
    | alloc hn _ => cases ihn hn
    | allocErrN hn => cases ihn hn; rfl
    | allocErrV hn _ => cases ihn hn
  case allocErrV ihn ihv =>
    cases h₂ with
    | alloc hn hv => cases ihn hn; cases ihv hv
    | allocErrN hn => cases ihn hn
    | allocErrV hn hv => cases ihn hn; cases ihv hv; rfl
  case get iha ihi =>
    cases h₂ with
    | get ha hi => cases iha ha; cases ihi hi; rfl
    | getErrA ha => cases iha ha
    | getErrI ha hi => cases iha ha; cases ihi hi
  case getErrA iha =>
    cases h₂ with
    | get ha _ => cases iha ha
    | getErrA ha => cases iha ha; rfl
    | getErrI ha _ => cases iha ha
  case getErrI iha ihi =>
    cases h₂ with
    | get ha hi => cases iha ha; cases ihi hi
    | getErrA ha => cases iha ha
    | getErrI ha hi => cases iha ha; cases ihi hi; rfl
  case set iha ihi ihv =>
    cases h₂ with
    | set ha hi hv => cases iha ha; cases ihi hi; cases ihv hv; rfl
    | setErrA ha => cases iha ha
    | setErrI ha hi => cases iha ha; cases ihi hi
    | setErrV ha hi hv => cases iha ha; cases ihi hi; cases ihv hv
  case setErrA iha =>
    cases h₂ with
    | set ha _ _ => cases iha ha
    | setErrA ha => cases iha ha; rfl
    | setErrI ha _ => cases iha ha
    | setErrV ha _ _ => cases iha ha
  case setErrI iha ihi =>
    cases h₂ with
    | set ha hi _ => cases iha ha; cases ihi hi
    | setErrA ha => cases iha ha
    | setErrI ha hi => cases iha ha; cases ihi hi; rfl
    | setErrV ha hi _ => cases iha ha; cases ihi hi
  case setErrV iha ihi ihv =>
    cases h₂ with
    | set ha hi hv => cases iha ha; cases ihi hi; cases ihv hv
    | setErrA ha => cases iha ha
    | setErrI ha hi => cases iha ha; cases ihi hi
    | setErrV ha hi hv => cases iha ha; cases ihi hi; cases ihv hv; rfl
  case len iha =>
    cases h₂ with
    | len ha => cases iha ha; rfl
    | lenErr ha => cases iha ha
  case lenErr iha =>
    cases h₂ with
    | len ha => cases iha ha
    | lenErr ha => cases iha ha; rfl
  case ref ihe =>
    cases h₂ with
    | ref he => cases ihe he; rfl
    | refErr he => cases ihe he
  case refErr ihe =>
    cases h₂ with
    | ref he => cases ihe he
    | refErr he => cases ihe he; rfl
  case deref ihr =>
    cases h₂ with
    | deref hr => cases ihr hr; rfl
    | derefErr hr => cases ihr hr
  case derefErr ihr =>
    cases h₂ with
    | deref hr => cases ihr hr
    | derefErr hr => cases ihr hr; rfl
  case assign ihr ihe =>
    cases h₂ with
    | assign hr he => cases ihr hr; cases ihe he; rfl
    | assignErrR hr => cases ihr hr
    | assignErrV hr he => cases ihr hr; cases ihe he
  case assignErrR ihr =>
    cases h₂ with
    | assign hr _ => cases ihr hr
    | assignErrR hr => cases ihr hr; rfl
    | assignErrV hr _ => cases ihr hr
  case assignErrV ihr ihe =>
    cases h₂ with
    | assign hr he => cases ihr hr; cases ihe he
    | assignErrR hr => cases ihr hr
    | assignErrV hr he => cases ihr hr; cases ihe he; rfl
  case exn ihe =>
    cases h₂ with
    | exn he => cases ihe he; rfl
    | exnErr he => cases ihe he
  case exnErr ihe =>
    cases h₂ with
    | exn he => cases ihe he
    | exnErr he => cases ihe he; rfl
  case raise hx ihe =>
    cases h₂ with
    | raise he _ => cases ihe he; rfl
    | raiseNotExn he hx' => cases ihe he; rw [hx] at hx'; cases hx'
    | raiseErr he => cases ihe he
  case raiseNotExn hx ihe =>
    cases h₂ with
    | raise he hx' => cases ihe he; rw [hx] at hx'; cases hx'
    | raiseNotExn he _ => cases ihe he; rfl
    | raiseErr he => cases ihe he
  case raiseErr ihe =>
    cases h₂ with
    | raise he _ => cases ihe he
    | raiseNotExn he _ => cases ihe he
    | raiseErr he => cases ihe he; rfl

end Diva
