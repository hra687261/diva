import Diva.Semantics

/-!
# Executable interpreter

`eval fuel ρ μ e` runs `e` with the store `μ` and returns a value, a runtime
error, or `outOfFuel` when the fuel (a bound on the recursion depth) ran out.
`eval_sound` proves that any outcome `eval` returns agrees with `Semantics.Eval`.
-/

namespace Diva

/-- Running the interpreter gives: a value (some (.ok _, μ)), a runtime error
    (some (.err _, μ)), each with the final store μ, or out of fuel (none).
    Option (Outcome × Store) is intentional to split the semantics from runtime
    results.
-/
abbrev Result := Option (Outcome × Store)
@[match_pattern] abbrev Result.ok (v : Value) (μ : Store) : Result := some (.ok v, μ)
@[match_pattern] abbrev Result.err (k : Err) (μ : Store) : Result := some (.err k, μ)
@[match_pattern] abbrev Result.outOfFuel : Result := none

def eval : Nat → Env → Store → Expr → Result
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, ρ, μ, e =>
    match e with
    | .int n  => .ok (.int n) μ
    | .bool b => .ok (.bool b) μ
    | .unit   => .ok .unit μ
    | .nil    => .ok .nil μ
    | .var x  =>
      match ρ.lookup x with
      | some v => .ok v μ
      | none   => .err .unbound μ
    | .lam x b => .ok (.clos none x b ρ) μ
    | .letrec f x e1 e2 =>
      eval fuel ((f, .clos (some f) x e1 ρ) :: ρ) μ e2
    | .app f a =>
      match eval fuel ρ μ f with
      | .ok vf μ₁ =>
        match eval fuel ρ μ₁ a with
        | .ok va μ₂ =>
          match vf with
          | .clos s x b ρ' => eval fuel (callEnv s x b ρ' va) μ₂ b
          | _ => .err .typeError μ₂
        | r => r
      | r => r
    | .letin x e1 e2 =>
      match eval fuel ρ μ e1 with
      | .ok v μ₁ => eval fuel ((x, v) :: ρ) μ₁ e2
      | r => r
    | .ite c t e =>
      match eval fuel ρ μ c with
      | .ok (.bool true) μ₁  => eval fuel ρ μ₁ t
      | .ok (.bool false) μ₁ => eval fuel ρ μ₁ e
      | .ok _ μ₁ => .err .typeError μ₁
      | r => r
    | .binop op a b =>
      match eval fuel ρ μ a with
      | .ok va μ₁ =>
        match eval fuel ρ μ₁ b with
        | .ok vb μ₂ => some (op.denote va vb, μ₂)
        | r => r
      | r => r
    | .cons a b =>
      match eval fuel ρ μ a with
      | .ok va μ₁ =>
        match eval fuel ρ μ₁ b with
        | .ok vb μ₂ =>
          if vb.isList
          then .ok (.cons va vb) μ₂
          else .err .typeError μ₂
        | r => r
      | r => r
    | .matchList s n x xs c =>
      match eval fuel ρ μ s with
      | .ok .nil μ₁ => eval fuel ρ μ₁ n
      | .ok (.cons vh vt) μ₁ => eval fuel ((xs, vt) :: (x, vh) :: ρ) μ₁ c
      | .ok _ μ₁ => .err .typeError μ₁
      | r => r
    | .assert c =>
      match eval fuel ρ μ c with
      | .ok (.bool true) μ₁  => .ok .unit μ₁
      | .ok (.bool false) μ₁ => .err .assertFail μ₁
      | .ok _ μ₁ => .err .typeError μ₁
      | r => r
    | .alloc _ n v =>
      match eval fuel ρ μ n with
      | .ok vn μ₁ =>
        match eval fuel ρ μ₁ v with
        | .ok vv μ₂ => some (allocV μ₂ vn vv)
        | r => r
      | r => r
    | .get a i =>
      match eval fuel ρ μ a with
      | .ok va μ₁ =>
        match eval fuel ρ μ₁ i with
        | .ok vi μ₂ => some (getV μ₂ va vi, μ₂)
        | r => r
      | r => r
    | .set a i v =>
      match eval fuel ρ μ a with
      | .ok va μ₁ =>
        match eval fuel ρ μ₁ i with
        | .ok vi μ₂ =>
          match eval fuel ρ μ₂ v with
          | .ok vv μ₃ => some (setV μ₃ va vi vv)
          | r => r
        | r => r
      | r => r
    | .len a =>
      match eval fuel ρ μ a with
      | .ok va μ₁ => some (lenV μ₁ va, μ₁)
      | r => r
    | .ref _ e =>
      match eval fuel ρ μ e with
      | .ok v μ₁ => some (refV μ₁ v)
      | r => r
    | .deref r =>
      match eval fuel ρ μ r with
      | .ok vr μ₁ => some (derefV μ₁ vr, μ₁)
      | r => r
    | .assign r e =>
      match eval fuel ρ μ r with
      | .ok vr μ₁ =>
        match eval fuel ρ μ₁ e with
        | .ok v μ₂ => some (assignV μ₂ vr v)
        | r => r
      | r => r
    | .exn c e =>
      match eval fuel ρ μ e with
      | .ok v μ₁ => .ok (.exn c v) μ₁
      | r => r
    | .raise e =>
      match eval fuel ρ μ e with
      | .ok v μ₁ =>
        if v.isExn then .err (.exn v) μ₁ else .err .typeError μ₁
      | r => r
    | .tryw e x h =>
      match eval fuel ρ μ e with
      | .err (.exn v) μ₁ => eval fuel ((x, v) :: ρ) μ₁ h
      | r => r
    | .exnCase s c x hit miss =>
      match eval fuel ρ μ s with
      | .ok (.exn c' v) μ₁ =>
        if c' = c then eval fuel ((x, v) :: ρ) μ₁ hit else eval fuel ρ μ₁ miss
      | .ok _ μ₁ => .err .typeError μ₁
      | r => r

/-- **Interpreter soundness**: whatever the interpreter returns is what `Eval` says. -/
theorem eval_sound :
    ∀ {fuel ρ μ e r μ'}, eval fuel ρ μ e = some (r, μ') → Eval ρ μ e r μ' := by
  intro fuel
  induction fuel
  case zero =>
    intro ρ μ e r μ' h
    simp [eval] at h
  case succ n ih =>
    intro ρ μ e r μ' h
    cases e <;> simp [eval] at h
    case int _ =>
      -- obtain ⟨h1, h2⟩ := h
      -- subst h1
      -- subst h2
      obtain ⟨h1, h2⟩ := h; subst h1 h2
      exact Eval.int
    case bool b =>
      obtain ⟨h1, h2⟩ := h; subst h1 h2
      exact Eval.bool
    case unit =>
      obtain ⟨h1, h2⟩ := h; subst h1 h2
      exact Eval.unit
    case var =>
      split at h
      case h_1 v hl =>
        cases h
        exact .var hl
      case h_2 hl =>
        cases h
        exact .varErr hl
    case app =>
      split at h
      case h_1 v μ₁ hl =>
        split at h
        case h_1 va μ₂ ha =>
          split at h
          case h_1 s x b ρ' =>
            exact .app (ih hl) (ih ha) (ih h)
          case h_2 hnc =>
            cases h
            have hv : v.isClos = false := by
              cases v
              case clos s x b ρ' =>
                have c := hnc s x b ρ'
                exact absurd rfl c
              all_goals rfl
            exact .appNotFn (ih hl) hv (ih ha)
        case h_2 hna =>
          cases r with
          | ok va => exact absurd h (hna va μ')
          | err k => exact .appErrA (ih hl) (ih h)
      case h_2 hnf =>
        cases r with
        | ok vf => exact absurd h (hnf vf μ')
        | err k => exact .appErrF (ih h)
    case lam x body =>
      obtain ⟨h1, h2⟩ := h; subst h1 h2
      exact Eval.lam
    case letin =>
      split at h
      case h_1 v μ₁ h1 => exact .letin (ih h1) (ih h)
      case h_2 hne =>
        cases r with
        | ok v => exact absurd h (hne v μ')
        | err k => exact .letinErr (ih h)
    case letrec =>
      exact .letrec (ih h)
    case ite =>
      split at h
      case h_1 μ₁ hc => exact .ifT (ih hc) (ih h)
      case h_2 μ₁ hc => exact .ifF (ih hc) (ih h)
      case h_3 _ v μ₁ hnt hnf hc =>
        cases h
        have hv : v.isBool = false := by
          cases v
          case bool b =>
            cases b
            · exact absurd rfl hnf
            · exact absurd rfl hnt
          all_goals rfl
        exact .ifNotBool (ih hc) hv
      case h_4 hnc =>
        cases r with
        | ok v => exact absurd h (hnc v μ')
        | err k => exact .ifErr (ih h)
    case binop =>
      split at h
      case h_1 va μ₁ ha =>
        split at h
        case h_1 vb μ₂ hb =>
          cases h
          exact .binop (ih ha) (ih hb)
        case h_2 hnb =>
          cases r with
          | ok v => exact absurd h (hnb v μ')
          | err k => exact .binopErrR (ih ha) (ih h)
      case h_2 hna =>
        cases r with
        | ok v => exact absurd h (hna v μ')
        | err k => exact .binopErrL (ih h)
    case nil =>
      obtain ⟨h1, h2⟩ := h; subst h1 h2
      exact Eval.nil
    case cons =>
      split at h
      case h_1 va μ₁ ha =>
        split at h
        case h_1 vb μ₂ hb =>
          split at h
          case isTrue hl =>
            cases h
            exact .cons (ih ha) (ih hb) hl
          case isFalse hl =>
            cases h
            exact .consNotList (ih ha) (ih hb) (by simpa using hl)
        case h_2 hnb =>
          cases r with
          | ok v => exact absurd h (hnb v μ')
          | err k => exact .consErrR (ih ha) (ih h)
      case h_2 hna =>
        cases r with
        | ok v => exact absurd h (hna v μ')
        | err k => exact .consErrL (ih h)
    case matchList =>
      split at h
      case h_1 μ₁ hs => exact .matchNil (ih hs) (ih h)
      case h_2 vh vt μ₁ hs => exact .matchCons (ih hs) (ih h)
      case h_3 _ v μ₁ hnn hnc hs =>
        cases h
        have hv : v.isList = false := by
          cases v
          case nil => exact absurd rfl hnn
          case cons vh vt => exact absurd rfl (hnc vh vt)
          all_goals rfl
        exact .matchNotList (ih hs) hv
      case h_4 hns =>
        cases r with
        | ok v => exact absurd h (hns v μ')
        | err k => exact .matchErr (ih h)
    case assert =>
      split at h
      case h_1 μ₁ hc =>
        cases h
        exact .assert (ih hc)
      case h_2 μ₁ hc =>
        cases h
        exact .assertF (ih hc)
      case h_3 _ v μ₁ hnt hnf hc =>
        cases h
        have hv : v.isBool = false := by
          cases v
          case bool b =>
            cases b
            · exact absurd rfl hnf
            · exact absurd rfl hnt
          all_goals rfl
        exact .assertNotBool (ih hc) hv
      case h_4 hnc =>
        cases r with
        | ok v => exact absurd h (hnc v μ')
        | err k => exact .assertErr (ih h)
    case alloc =>
      split at h
      case h_1 vn μ₁ hn =>
        split at h
        case h_1 vv μ₂ hv =>
          injection h with h
          simp only [Prod.ext_iff] at h
          obtain ⟨h1, h2⟩ := h; subst h1 h2
          exact .alloc (ih hn) (ih hv)
        case h_2 hnv =>
          cases r with
          | ok v => exact absurd h (hnv v μ')
          | err k => exact .allocErrV (ih hn) (ih h)
      case h_2 hnn =>
        cases r with
        | ok v => exact absurd h (hnn v μ')
        | err k => exact .allocErrN (ih h)
    case get =>
      split at h
      case h_1 va μ₁ ha =>
        split at h
        case h_1 vi μ₂ hi =>
          injection h with h; injection h with h1 h2; subst h1 h2
          exact .get (ih ha) (ih hi)
        case h_2 hni =>
          cases r with
          | ok v => exact absurd h (hni v μ')
          | err k => exact .getErrI (ih ha) (ih h)
      case h_2 hna =>
        cases r with
        | ok v => exact absurd h (hna v μ')
        | err k => exact .getErrA (ih h)
    case set =>
      split at h
      case h_1 va μ₁ ha =>
        split at h
        case h_1 vi μ₂ hi =>
          split at h
          case h_1 vv μ₃ hv =>
            injection h with h
            simp only [Prod.ext_iff] at h
            obtain ⟨h1, h2⟩ := h; subst h1 h2
            exact .set (ih ha) (ih hi) (ih hv)
          case h_2 hnv =>
            cases r with
            | ok v => exact absurd h (hnv v μ')
            | err k => exact .setErrV (ih ha) (ih hi) (ih h)
        case h_2 hni =>
          cases r with
          | ok v => exact absurd h (hni v μ')
          | err k => exact .setErrI (ih ha) (ih h)
      case h_2 hna =>
        cases r with
        | ok v => exact absurd h (hna v μ')
        | err k => exact .setErrA (ih h)
    case len =>
      split at h
      case h_1 va μ₁ ha =>
        injection h with h; injection h with h1 h2; subst h1 h2
        exact .len (ih ha)
      case h_2 hna =>
        cases r with
        | ok v => exact absurd h (hna v μ')
        | err k => exact .lenErr (ih h)
    case ref =>
      split at h
      case h_1 v μ₁ he =>
        injection h with h
        simp only [Prod.ext_iff] at h
        obtain ⟨h1, h2⟩ := h; subst h1 h2
        exact .ref (ih he)
      case h_2 hne =>
        cases r with
        | ok v => exact absurd h (hne v μ')
        | err k => exact .refErr (ih h)
    case deref =>
      split at h
      case h_1 vr μ₁ hr =>
        injection h with h; injection h with h1 h2; subst h1 h2
        exact .deref (ih hr)
      case h_2 hnr =>
        cases r with
        | ok v => exact absurd h (hnr v μ')
        | err k => exact .derefErr (ih h)
    case assign =>
      split at h
      case h_1 vr μ₁ hr =>
        split at h
        case h_1 v μ₂ he =>
          injection h with h
          simp only [Prod.ext_iff] at h
          obtain ⟨h1, h2⟩ := h; subst h1 h2
          exact .assign (ih hr) (ih he)
        case h_2 hne =>
          cases r with
          | ok v => exact absurd h (hne v μ')
          | err k => exact .assignErrV (ih hr) (ih h)
      case h_2 hnr =>
        cases r with
        | ok v => exact absurd h (hnr v μ')
        | err k => exact .assignErrR (ih h)
    case exn =>
      split at h
      case h_1 v μ₁ he =>
        cases h
        exact .exn (ih he)
      case h_2 hne =>
        cases r with
        | ok v => exact absurd h (hne v μ')
        | err k => exact .exnErr (ih h)
    case raise =>
      split at h
      case h_1 v μ₁ he =>
        split at h
        case isTrue hx =>
          cases h
          exact .raise (ih he) hx
        case isFalse hx =>
          cases h
          exact .raiseNotExn (ih he) (by simpa using hx)
      case h_2 hne =>
        cases r with
        | ok v => exact absurd h (hne v μ')
        | err k => exact .raiseErr (ih h)
    case tryw =>
      split at h
      case h_1 v μ₁ he => exact .tryCatch (ih he) (ih h)
      case h_2 hne =>
        cases r with
        | ok v => exact .tryOk (ih h)
        | err k =>
          cases k
          case exn v => exact absurd h (hne v μ')
          all_goals exact .tryErr (ih h) rfl
    case exnCase =>
      split at h
      case h_1 c' v μ₁ hs =>
        split at h
        case isTrue hc => subst hc; exact .exnHit (ih hs) (ih h)
        case isFalse hc => exact .exnMiss (ih hs) hc (ih h)
      case h_2 _ v μ₁ hne hs =>
        cases h
        have hv : v.isExn = false := by
          cases v
          case exn c' v' => exact absurd rfl (hne c' v')
          all_goals rfl
        exact .exnCaseNotExn (ih hs) hv
      case h_3 hns =>
        cases r with
        | ok v => exact absurd h (hns v μ')
        | err k => exact .exnCaseErr (ih h)

def ppValue : Value → String
  | .int n  => toString n
  | .bool b => toString b
  | .unit => "()"
  | .clos .. => "<fun>"
  | .nil => "[]"
  | .cons a b => s!"({ppValue a} :: {ppValue b})"
  | .arr l => s!"<array {l}>"
  | .ref l => s!"<ref {l}>"
  | .exn c .unit => c
  | .exn c v => s!"({c} {ppValue v})"

instance : ToString Value := ⟨ppValue⟩

def ppErr : Err → String
  | .divZero    => "division by zero"
  | .assertFail => "assertion failed"
  | .typeError  => "type error"
  | .unbound    => "unbound variable"
  | .outOfBounds => "index out of bounds"
  | .exn v       => s!"uncaught exception {ppValue v}"

def ppOutcome : Outcome → String
  | .ok v  => ppValue v
  | .err k => s!"error: {ppErr k}"

instance : ToString Outcome := ⟨ppOutcome⟩

end Diva
