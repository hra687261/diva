import Diva.AbsInt.Aeval

/-!
# Possible errors: soundness

`mayFail H σ e` (in `Aeval.lean`) says whether `e` may end in an error: division by
zero, a failed `assert`, a type error (like `1 + true`), an unbound variable, or an
exception. `false` means `e` certainly doesn't fail, and `mayFail_sound` proves it.

It uses `aeval` for the values of the parts of `e`. For example, `10 / x` may fail
only if `x` may be `0`. A call may fail unless the function's summary says that its
body doesn't fail, and the argument is in the summary's precondition.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

variable {A : Type} [NumDomain A]

theorem Flat.not_mem_bot {v : Value} : ¬ (Flat.bot : Flat A).mem v := by
  intro h
  cases v
  case int n => exact bot_sound n h
  case bool b => cases b <;> simp [Flat.mem, Flat.bot] at h
  all_goals simp [Flat.mem, Flat.bot] at h

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

/-- A call of something that isn't a closure may fail. -/
theorem callMayFail_notFn {af aa : AVal A} {vf : Value} (hf : af.mem vf)
    (hv : vf.isClos = false) : callMayFail af aa = true := by
  unfold callMayFail
  split
  next S hS =>
    cases hc : af.toFlat.leq Flat.bot && aa.flat.leq S.pre && !S.fails
    · rfl
    · simp only [Bool.and_eq_true] at hc
      cases hf with
      | flat hf =>
        -- `af` describes no value but closures of its summary
        exact absurd (Flat.mem_leq hf hc.1.1) Flat.not_mem_bot
      | sum =>
        -- a closure
        simp [Value.isClos] at hv
  next => rfl

/-- A call whose body fails may fail. `hb`: any check of the body says that it may
    fail (the induction hypothesis of `mayFail_sound_aux`). -/
theorem callMayFail_sound {af aa : AVal A} {s : Option String} {x : String} {b : Expr}
    {ρ' : Env} {va : Value} (hf : af.mem (.clos s x b ρ')) (ha : aa.mem va)
    (hb : ∀ (H : Hints A) (σ : AEnv A), σ.Describes (callEnv s x b ρ' va) →
      σ.Bound (callEnv s x b ρ' va) → mayFail H σ b = true) :
    callMayFail af aa = true := by
  unfold callMayFail
  split
  next S hS =>
    cases hc : af.toFlat.leq Flat.bot && aa.flat.leq S.pre && !S.fails
    · rfl
    · -- the three checks pass
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨hbot, hpre⟩, hF⟩ := hc
      cases hf with
      | flat hf => exact absurd (Flat.mem_leq hf hbot) Flat.not_mem_bot
      | sum H σ hS' hP _ hF' hd hB hcheck hcheckF =>
        -- the closure's summary is `S`
        rw [hS] at hS'
        cases hS'
        -- the body was checked not to fail with an argument in `S₀.pre`
        have hv := hP va (Flat.mem_leq (AVal.mem_flat ha) hpre)
        have hok := hcheckF (hF' hF)
        -- but it fails
        have hfail := hb H _ (AEnv.Describes.body hd hB hcheck hcheckF hv) (AEnv.Bound.body hB)
        simp [hok] at hfail
  next => rfl

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
  | app hf ha _ _ _ ihb =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    refine Or.inr (callMayFail_sound (aeval_sound hσ hB hf) (aeval_sound hσ hB ha) ?_)
    intro H' σ' hd hb
    exact ihb (H := H') hd hb hr
  | appNotFn hf hv =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inr (callMayFail_notFn (aeval_sound hσ hB hf) hv)
  | appErrF _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inl (Or.inl (ih hσ hB hr))
  | appErrA _ _ _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inl (Or.inr (ih hσ hB hr))
  | letin h1 _ _ ih2 =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inr (ih2 (hσ.cons (aeval_sound hσ hB h1)) hB.cons hr)
  | letinErr _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inl (ih hσ hB hr)
  | letrec _ ih =>
    intro H σ k hσ hB hr
    -- `f` has the same value as in `aeval`
    exact ih (hσ.cons (letrecVal_mem hσ hB)) hB.cons hr
  | binop ha hb =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inr (opMayFail_sound (aeval_sound hσ hB ha) (aeval_sound hσ hB hb) hr)
  | binopErrL _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inl (Or.inl (ih hσ hB hr))
  | binopErrR _ _ _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inl (Or.inr (ih hσ hB hr))
  | consNotList _ hb hv =>
    intro H σ k hσ hB hr
    simp [mayFail, mayFailM, not_within_list (aeval_sound hσ hB hb) hv]
  | consErrL _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inl (Or.inl (ih hσ hB hr))
  | consErrR _ _ _ ih =>
    intro H σ k hσ hB hr
    simp only [mayFail, mayFailM, Bool.or_eq_true]
    exact Or.inl (Or.inr (ih hσ hB hr))
  | ifT hc _ _ iht =>
    intro H σ k hσ hB hr
    -- the `then` branch can be taken, and it fails
    have htt : (aevalM false H σ _).tt = true := AVal.mem_tt (aeval_sound hσ hB hc)
    obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
    have hft := iht (H := H) hdt (AEnv.assume_bound hB hst) hr
    simp [mayFail, mayFailM, htt, hst, hft]
  | ifF hc _ _ ihe =>
    intro H σ k hσ hB hr
    have hff : (aevalM false H σ _).ff = true := AVal.mem_ff (aeval_sound hσ hB hc)
    obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
    have hfe := ihe (H := H) hde (AEnv.assume_bound hB hse) hr
    simp [mayFail, mayFailM, hff, hse, hfe]
  | ifNotBool hc hv =>
    intro H σ k hσ hB hr
    simp [mayFail, mayFailM, not_within_bool (aeval_sound hσ hB hc) hv]
  | ifErr _ ih =>
    intro H σ k hσ hB hr
    simp [mayFail, mayFailM, ih hσ hB hr]
  | assertF hc =>
    intro H σ k hσ hB hr
    simp [mayFail, mayFailM, AVal.mem_ff (aeval_sound hσ hB hc)]
  | assertNotBool hc hv =>
    intro H σ k hσ hB hr
    simp [mayFail, mayFailM, not_within_bool (aeval_sound hσ hB hc) hv]
  | assertErr _ ih =>
    intro H σ k hσ hB hr
    simp [mayFail, mayFailM, ih hσ hB hr]
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

/-- The empty abstract environment describes the empty environment. -/
theorem AEnv.Describes.nil : AEnv.Describes ([] : AEnv A) [] := by
  intro x v hx
  simp [List.lookup] at hx

omit [NumDomain A] in
/-- The empty abstract environment knows no variable. -/
theorem AEnv.Bound.nil : AEnv.Bound ([] : AEnv A) [] := by
  intro x hx
  simp [List.lookup] at hx

/-- **Safety**: a program without free variables that `mayFail` accepts never ends
    in an error, whatever the hints and the starting store. -/
theorem safe {H : Hints A} {e : Expr} {μ μ' : Store} {k : Err}
    (hok : mayFail H [] e = false) : ¬ Eval [] μ e (.err k) μ' := by
  intro h
  -- if it did, `mayFail` would say `true`
  have hfail := mayFail_sound (H := H) AEnv.Describes.nil AEnv.Bound.nil h
  rw [hok] at hfail
  cases hfail

end Diva.AbsInt
