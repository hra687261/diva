import Diva.AbsInt.Aeval

/-!
# Possible errors

`mayFail H σ e` says whether `e` may end in an error: division by zero, a failed
`assert`, a type error (like `1 + true`), an unbound variable, or an exception.
`false` means `e` certainly doesn't fail, and `mayFail_sound` proves it.

It uses `aeval` for the values of the parts of `e`. For example, `10 / x` may fail
only if `x` may be `0`.

Not done yet: a function call always may fail, because summaries don't say whether
the function's body may fail.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

variable {A : Type} [NumDomain A]

/-! ## Kinds of values -/

/-- Any integer, and nothing else. -/
def Flat.ints : Flat A := Flat.ofInt AbsDomain.top

/-- Any boolean, and nothing else. -/
def Flat.anyBool : Flat A := Flat.bools true true

/-- `a` describes only values that `k` describes. -/
def AVal.within (a : AVal A) (k : Flat A) : Bool := a.flat.leq k

/-- `op` may fail on values that `a` and `b` describe. -/
def opMayFail : BinOp → AVal A → AVal A → Bool
  | .add, a, b | .sub, a, b | .mul, a, b | .lt, a, b | .le, a, b | .gt, a, b
  | .ge, a, b => !(a.within Flat.ints && b.within Flat.ints)
  -- also when the divisor may be `0`
  | .div, a, b | .mod, a, b =>
    !(a.within Flat.ints && b.within Flat.ints) || (cmpEq b.int (const 0)).1
  -- `=` needs two integers or two booleans (or two `()`, not looked at here)
  | .eq, a, b | .ne, a, b =>
    !((a.within Flat.ints && b.within Flat.ints) ||
      (a.within Flat.anyBool && b.within Flat.anyBool))

/-- Whether `e` may end in an error, when `σ` describes the variables. -/
def mayFail (H : Hints A) (σ : AEnv A) : Expr → Bool
  | .int _ | .bool _ | .unit | .nil | .lam _ _ => false
  -- a variable `σ` knows is bound (see `AEnv.Bound`)
  | .var x => (σ.lookup x).isNone
  | .binop op a b =>
    mayFail H σ a || mayFail H σ b || opMayFail op (aeval H σ a) (aeval H σ b)
  | .cons a b => mayFail H σ a || mayFail H σ b || !(aeval H σ b).within Flat.listV
  | .letin x e1 e2 => mayFail H σ e1 || mayFail H ((x, aeval H σ e1) :: σ) e2
  | .letrec f _ _ e2 => mayFail H ((f, AVal.fnV) :: σ) e2
  | .ite c t e =>
    -- a branch counts only if it can be taken
    let ac := aeval H σ c
    mayFail H σ c || !ac.within Flat.anyBool ||
      (ac.tt && ((σ.assume c true).map (mayFail H · t)).getD false) ||
      (ac.ff && ((σ.assume c false).map (mayFail H · e)).getD false)
  | .assert c =>
    let ac := aeval H σ c
    mayFail H σ c || !ac.within Flat.anyBool || ac.ff
  | .exn _ e => mayFail H σ e
  -- calls, `raise`, `try`, lists, arrays and refs: not analysed yet
  | _ => true

/-! ## Soundness -/

/-- Every variable that `σ` knows is bound in `ρ`. -/
def AEnv.Bound (σ : AEnv A) (ρ : Env) : Prop :=
  ∀ x, (σ.lookup x).isSome = true → (ρ.lookup x).isSome = true

namespace AEnv

variable {σ σ' : AEnv A} {ρ : Env}

omit [NumDomain A] in
theorem Bound.cons {x : String} {a : AVal A} {v : Value} (hb : σ.Bound ρ) :
    AEnv.Bound ((x, a) :: σ) ((x, v) :: ρ) := by
  intro y hy
  by_cases hxy : y = x
  · subst hxy
    simp [List.lookup]
  · have hne : (y == x) = false := by simpa using hxy
    simp only [List.lookup, hne] at hy ⊢
    exact hb y hy

omit [NumDomain A] in
/-- A variable that isn't bound is unknown to `σ`. -/
theorem Bound.none {x : String} (hb : σ.Bound ρ) (hx : ρ.lookup x = none) :
    (σ.lookup x).isNone = true := by
  cases hs : σ.lookup x
  · rfl
  · have h := hb x (by simp [hs])
    simp [hx] at h

omit [NumDomain A] in
theorem bind_bound {e : Expr} {a : AVal A} (hb : σ.Bound ρ) : (σ.bind e a).Bound ρ := by
  cases e
  case var x =>
    by_cases hk : (σ.lookup x).isSome
    · -- `x` was already known
      simp only [bind, hk, ↓reduceIte]
      intro y hy
      by_cases hxy : y = x
      · subst hxy
        exact hb y hk
      · have hne : (y == x) = false := by simpa using hxy
        simp only [List.lookup, hne] at hy
        exact hb y hy
    · simp only [bind, hk]
      exact hb
  all_goals exact hb

theorem refineLt_bound {l r : Expr} (hb : σ.Bound ρ) (h : σ.refineLt l r = some σ') :
    σ'.Bound ρ := by
  unfold refineLt at h
  split at h
  · cases h
    exact bind_bound (bind_bound hb)
  · cases h

theorem refineLe_bound {l r : Expr} (hb : σ.Bound ρ) (h : σ.refineLe l r = some σ') :
    σ'.Bound ρ := by
  unfold refineLe at h
  split at h
  · cases h
    exact bind_bound (bind_bound hb)
  · cases h

theorem refineEq_bound {l r : Expr} (hb : σ.Bound ρ) (h : σ.refineEq l r = some σ') :
    σ'.Bound ρ := by
  unfold refineEq at h
  cases h
  exact bind_bound (bind_bound hb)

/-- Narrowing doesn't add variables. -/
theorem assume_bound {c : Expr} {b : Bool} (hb : σ.Bound ρ) (h : σ.assume c b = some σ') :
    σ'.Bound ρ := by
  cases c
  case binop op l r =>
    cases op <;> cases b <;> simp only [assume] at h
    case lt.true  => exact refineLt_bound hb h
    case lt.false => exact refineLe_bound hb h
    case le.true  => exact refineLe_bound hb h
    case le.false => exact refineLt_bound hb h
    case gt.true  => exact refineLt_bound hb h
    case gt.false => exact refineLe_bound hb h
    case ge.true  => exact refineLe_bound hb h
    case ge.false => exact refineLt_bound hb h
    case eq.true  => exact refineEq_bound hb h
    case ne.false => exact refineEq_bound hb h
    -- the other conditions don't narrow
    all_goals
      cases h
      exact hb
  all_goals
    simp only [assume] at h
    cases h
    exact hb

end AEnv

theorem within_mem {a : AVal A} {k : Flat A} {v : Value} (hw : a.within k = true)
    (h : a.mem v) : k.mem v :=
  Flat.mem_leq (AVal.mem_flat h) hw

theorem int_of_within {a : AVal A} {v : Value} (hw : a.within Flat.ints = true)
    (h : a.mem v) : ∃ n, v = .int n := by
  have hm := within_mem hw h
  cases v
  case int n => exact ⟨n, rfl⟩
  case bool b => cases b <;> simp [Flat.mem, Flat.ints, Flat.ofInt, Flat.bot] at hm
  all_goals simp [Flat.mem, Flat.ints, Flat.ofInt, Flat.bot] at hm

theorem bool_of_within {a : AVal A} {v : Value} (hw : a.within Flat.anyBool = true)
    (h : a.mem v) : ∃ b, v = .bool b := by
  have hm := within_mem hw h
  cases v
  case bool b => exact ⟨b, rfl⟩
  case int n => exact absurd hm (bot_sound n)
  all_goals simp [Flat.mem, Flat.anyBool, Flat.bools, Flat.bot] at hm

/-- A value that isn't a boolean: `a` doesn't describe only booleans. -/
theorem not_within_bool {a : AVal A} {v : Value} (h : a.mem v) (hv : v.isBool = false) :
    a.within Flat.anyBool = false := by
  cases hw : a.within Flat.anyBool
  · rfl
  · obtain ⟨b, rfl⟩ := bool_of_within hw h
    simp [Value.isBool] at hv

/-- A value that isn't a list: `a` doesn't describe only lists. -/
theorem not_within_list {a : AVal A} {v : Value} (h : a.mem v) (hv : v.isList = false) :
    a.within Flat.listV = false := by
  cases hw : a.within Flat.listV
  · rfl
  · have hm := within_mem hw h
    cases v
    case int n => exact absurd hm (bot_sound n)
    case bool b => cases b <;> simp [Flat.mem, Flat.listV, Flat.bot] at hm
    all_goals simp_all [Flat.mem, Flat.listV, Flat.bot, Value.isList]

theorem opMayFail_sound {op : BinOp} {a b : AVal A} {va vb : Value} {k : Err}
    (ha : a.mem va) (hb : b.mem vb) (h : op.denote va vb = .err k) :
    opMayFail op a b = true := by
  -- if `opMayFail` says no, the operands have the right kinds, so `op` succeeds
  cases hm : opMayFail op a b
  case true => rfl
  case false =>
    cases op
    case eq | ne =>
      simp only [opMayFail, Bool.not_eq_false', Bool.or_eq_true, Bool.and_eq_true] at hm
      rcases hm with ⟨hwa, hwb⟩ | ⟨hwa, hwb⟩
      · obtain ⟨x, rfl⟩ := int_of_within hwa ha
        obtain ⟨y, rfl⟩ := int_of_within hwb hb
        simp [BinOp.denote] at h
      · obtain ⟨x, rfl⟩ := bool_of_within hwa ha
        obtain ⟨y, rfl⟩ := bool_of_within hwb hb
        simp [BinOp.denote] at h
    case div | mod =>
      simp only [opMayFail, Bool.or_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true] at hm
      obtain ⟨⟨hwa, hwb⟩, hz⟩ := hm
      obtain ⟨x, rfl⟩ := int_of_within hwa ha
      obtain ⟨y, rfl⟩ := int_of_within hwb hb
      -- the error is a division by zero, but `b` can't be `0`
      have hy : y = 0 := by
        simp only [BinOp.denote] at h
        split at h
        · assumption
        · cases h
      subst hy
      have h0 := (cmpEq_sound (AVal.mem_int hb) (const_sound 0)).1 rfl
      simp [h0] at hz
    all_goals
      simp only [opMayFail, Bool.not_eq_false', Bool.and_eq_true] at hm
      obtain ⟨x, rfl⟩ := int_of_within hm.1 ha
      obtain ⟨y, rfl⟩ := int_of_within hm.2 hb
      simp [BinOp.denote] at h

theorem mayFail_sound_aux {ρ : Env} {μ μ' : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ') :
    ∀ {H : Hints A} {σ : AEnv A} {k : Err}, σ.Describes ρ → σ.Bound ρ → r = .err k →
      mayFail H σ e = true := by
  induction h with
  -- the rules giving a value: no error
  | int | bool | unit | nil | var | lam | cons | assert | exn =>
    intro H σ k hσ hB hr
    cases hr
  | varErr hx =>
    intro H σ k hσ hB hr
    exact hB.none hx
  | letin h1 _ _ ih2 =>
    intro H σ k hσ hB hr
    simp only [mayFail, Bool.or_eq_true]
    exact Or.inr (ih2 (hσ.cons (aeval_sound hσ h1)) hB.cons hr)
  | letinErr _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, Bool.or_eq_true]
    exact Or.inl (ih hσ hB hr)
  | letrec _ ih =>
    intro H σ k hσ hB hr
    -- `f` is a closure, which `fnV` describes
    exact ih (hσ.cons (.flat rfl)) hB.cons hr
  | binop ha hb =>
    intro H σ k hσ hB hr
    simp only [mayFail, Bool.or_eq_true]
    exact Or.inr (opMayFail_sound (aeval_sound hσ ha) (aeval_sound hσ hb) hr)
  | binopErrL _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, Bool.or_eq_true]
    exact Or.inl (Or.inl (ih hσ hB hr))
  | binopErrR _ _ _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, Bool.or_eq_true]
    exact Or.inl (Or.inr (ih hσ hB hr))
  | consNotList _ hb hv =>
    intro H σ k hσ hB hr
    simp [mayFail, not_within_list (aeval_sound hσ hb) hv]
  | consErrL _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, Bool.or_eq_true]
    exact Or.inl (Or.inl (ih hσ hB hr))
  | consErrR _ _ _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, Bool.or_eq_true]
    exact Or.inl (Or.inr (ih hσ hB hr))
  | ifT hc _ _ iht =>
    intro H σ k hσ hB hr
    -- the `then` branch can be taken, and it fails
    have htt : (aeval H σ _).tt = true := AVal.mem_tt (aeval_sound hσ hc)
    obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
    have hft := iht (H := H) hdt (AEnv.assume_bound hB hst) hr
    simp [mayFail, htt, hst, hft]
  | ifF hc _ _ ihe =>
    intro H σ k hσ hB hr
    have hff : (aeval H σ _).ff = true := AVal.mem_ff (aeval_sound hσ hc)
    obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
    have hfe := ihe (H := H) hde (AEnv.assume_bound hB hse) hr
    simp [mayFail, hff, hse, hfe]
  | ifNotBool hc hv =>
    intro H σ k hσ hB hr
    simp [mayFail, not_within_bool (aeval_sound hσ hc) hv]
  | ifErr _ ih =>
    intro H σ k hσ hB hr
    simp [mayFail, ih hσ hB hr]
  | assertF hc =>
    intro H σ k hσ hB hr
    simp [mayFail, AVal.mem_ff (aeval_sound hσ hc)]
  | assertNotBool hc hv =>
    intro H σ k hσ hB hr
    simp [mayFail, not_within_bool (aeval_sound hσ hc) hv]
  | assertErr _ ih =>
    intro H σ k hσ hB hr
    simp [mayFail, ih hσ hB hr]
  | exnErr _ ih =>
    intro H σ k hσ hB hr
    exact ih hσ hB hr
  -- the expressions not analysed yet: `mayFail` says `true`
  | _ =>
    intro H σ k hσ hB hr
    rfl

/-- **Soundness**: if `e` ends in an error, `mayFail` says it may. So `false` means
    that `e` certainly doesn't fail. -/
theorem mayFail_sound {H : Hints A} {σ : AEnv A} {ρ : Env} {μ μ' : Store} {e : Expr}
    {k : Err} (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (h : Eval ρ μ e (.err k) μ') :
    mayFail H σ e = true :=
  mayFail_sound_aux h hσ hB rfl

end Diva.AbsInt
