import Diva.Semantics

/-!
# Executable interpreter

`eval fuel ρ e` runs `e` and returns a value, a runtime error, or `outOfFuel`
when the fuel (a bound on the recursion depth) ran out.
`eval_sound` proves that any outcome `eval` returns agrees with `Semantics.Eval`.
-/

namespace Diva

/-- Running the interpreter gives: a value (some (.ok _)), a runtime error
    (some (.error _)), or out of fuel (none).
    Option Outcome is intentional to split the semantics from runtime results.
-/
abbrev Result := Option Outcome
@[match_pattern] abbrev Result.ok (v : Value) : Result := some (.ok v)
@[match_pattern] abbrev Result.err (k : Err) : Result := some (.err k)
@[match_pattern] abbrev Result.outOfFuel : Result := none

def eval : Nat → Env → Expr → Result
  | 0, _, _ => .outOfFuel
  | fuel + 1, ρ, e =>
    match e with
    | .int n  => .ok (.int n)
    | .bool b => .ok (.bool b)
    | .unit   => .ok .unit
    | .nil    => .ok .nil
    | .var x  =>
      match ρ.lookup x with
      | some v => .ok v
      | none   => .err .unbound
    | .lam x b => .ok (.clos none x b ρ)
    | .letrec f x e1 e2 =>
      eval fuel ((f, .clos (some f) x e1 ρ) :: ρ) e2
    | .app f a =>
      match eval fuel ρ f with
      | .ok vf =>
        match eval fuel ρ a with
        | .ok va =>
          match vf with
          | .clos s x b ρ' => eval fuel (callEnv s x b ρ' va) b
          | _ => .err .typeError
        | r => r
      | r => r
    | .letin x e1 e2 =>
      match eval fuel ρ e1 with
      | .ok v => eval fuel ((x, v) :: ρ) e2
      | r => r
    | .ite c t e =>
      match eval fuel ρ c with
      | .ok (.bool true)  => eval fuel ρ t
      | .ok (.bool false) => eval fuel ρ e
      | .ok _ => .err .typeError
      | r => r
    | .binop op a b =>
      match eval fuel ρ a with
      | .ok va =>
        match eval fuel ρ b with
        | .ok vb => some (op.denote va vb)
        | r => r
      | r => r
    | .cons a b =>
      match eval fuel ρ a with
      | .ok va =>
        match eval fuel ρ b with
        | .ok vb =>
          if vb.isList
          then .ok (.cons va vb)
          else .err .typeError
        | r => r
      | r => r
    | .matchList s n x xs c =>
      match eval fuel ρ s with
      | .ok .nil => eval fuel ρ n
      | .ok (.cons vh vt) => eval fuel ((xs, vt) :: (x, vh) :: ρ) c
      | .ok _ => .err .typeError
      | r => r
    | .assert c =>
      match eval fuel ρ c with
      | .ok (.bool true)  => .ok .unit
      | .ok (.bool false) => .err .assertFail
      | .ok _ => .err .typeError
      | r => r

/-- **Interpreter soundness**: whatever the interpreter returns is what `Eval` says. -/
theorem eval_sound : ∀ {fuel ρ e r}, eval fuel ρ e = some r → Eval ρ e r := by
  intro fuel
  induction fuel
  case zero =>
    intro ρ e r h
    simp [eval] at h
  case succ n ih =>
    intro ρ e r h
    cases e <;> simp [eval] at h
    case int _ =>
      subst h
      exact Eval.int
    case bool b =>
      subst h
      exact Eval.bool
    case unit =>
      subst h
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
      case h_1 v hl =>
        split at h
        case h_1 va ha =>
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
          | ok va => exact absurd h (hna va)
          | err k => exact .appErrA (ih hl) (ih h)
      case h_2 hnf =>
        cases r with
        | ok vf => exact absurd h (hnf vf)
        | err k => exact .appErrF (ih h)
    case lam x body =>
      subst h
      exact Eval.lam
    case letin =>
      split at h
      case h_1 v h1 => exact .letin (ih h1) (ih h)
      case h_2 hne =>
        cases r with
        | ok v => exact absurd h (hne v)
        | err k => exact .letinErr (ih h)
    case letrec =>
      exact .letrec (ih h)
    case ite =>
      split at h
      case h_1 hc => exact .ifT (ih hc) (ih h)
      case h_2 hc => exact .ifF (ih hc) (ih h)
      case h_3 _ v hnt hnf hc =>
        cases h
        have hv : v.isBool = false := by
          cases v
          case bool b =>
            cases b
            case false => exact absurd rfl hnf
            case true => exact absurd rfl hnt
          all_goals rfl
        exact .ifNotBool (ih hc) hv
      case h_4 hnc =>
        cases r with
        | ok v => exact absurd h (hnc v)
        | err k => exact .ifErr (ih h)
    case binop =>
      split at h
      case h_1 va ha =>
        split at h
        case h_1 vb hb =>
          cases h
          exact .binop (ih ha) (ih hb)
        case h_2 hnb =>
          cases r with
          | ok v => exact absurd h (hnb v)
          | err k => exact .binopErrR (ih ha) (ih h)
      case h_2 hna =>
        cases r with
        | ok v => exact absurd h (hna v)
        | err k => exact .binopErrL (ih h)
    case nil =>
      subst h
      exact Eval.nil
    case cons =>
      split at h
      case h_1 va ha =>
        split at h
        case h_1 vb hb =>
          split at h
          case isTrue hl =>
            cases h
            exact .cons (ih ha) (ih hb) hl
          case isFalse hl =>
            cases h
            exact .consNotList (ih ha) (ih hb) (by simpa using hl)
        case h_2 hnb =>
          cases r with
          | ok v => exact absurd h (hnb v)
          | err k => exact .consErrR (ih ha) (ih h)
      case h_2 hna =>
        cases r with
        | ok v => exact absurd h (hna v)
        | err k => exact .consErrL (ih h)
    case matchList =>
      split at h
      case h_1 hs => exact .matchNil (ih hs) (ih h)
      case h_2 vh vt hs => exact .matchCons (ih hs) (ih h)
      case h_3 _ v hnn hnc hs =>
        cases h
        have hv : v.isList = false := by
          cases v
          case nil => exact absurd rfl hnn
          case cons vh vt => exact absurd rfl (hnc vh vt)
          all_goals rfl
        exact .matchNotList (ih hs) hv
      case h_4 hns =>
        cases r with
        | ok v => exact absurd h (hns v)
        | err k => exact .matchErr (ih h)
    case assert =>
      split at h
      case h_1 hc =>
        cases h
        exact .assert (ih hc)
      case h_2 hc =>
        cases h
        exact .assertF (ih hc)
      case h_3 _ v hnt hnf hc =>
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
        | ok v => exact absurd h (hnc v)
        | err k => exact .assertErr (ih h)

def ppValue : Value → String
  | .int n  => toString n
  | .bool b => toString b
  | .unit => "()"
  | .clos .. => "<fun>"
  | .nil => "[]"
  | .cons a b => s!"({ppValue a} :: {ppValue b})"

instance : ToString Value := ⟨ppValue⟩

def ppErr : Err → String
  | .divZero    => "division by zero"
  | .assertFail => "assertion failed"
  | .typeError  => "type error"
  | .unbound    => "unbound variable"

def ppOutcome : Outcome → String
  | .ok v  => ppValue v
  | .err k => s!"error: {ppErr k}"

instance : ToString Outcome := ⟨ppOutcome⟩

end Diva
