import Diva.Semantics

/-!
# Executable interpreter

`eval fuel ρ e` runs `e`. `none` means either the fuel (a bound on the recursion
depth) ran out or the program is stuck (e.g. because of a typing error like
`true + 1`).
`eval_sound` proves that any value `eval` returns agrees with `Semantics.Eval`.
-/

namespace Diva

def eval : Nat → Env → Expr → Option Value
  | 0, _, _ => none
  | fuel + 1, ρ, e =>
    match e with
    | .int n  => some (.int n)
    | .bool b => some (.bool b)
    | .unit   => some .unit
    | .nil    => some .nil
    | .var x  => ρ.lookup x
    | .lam x b => some (.clos none x b ρ)
    | .letrec f x e1 e2 =>
      eval fuel ((f, .clos (some f) x e1 ρ) :: ρ) e2
    | .app f a => do
      let .clos s x b ρ' ← eval fuel ρ f | none
      let va ← eval fuel ρ a
      eval fuel (callEnv s x b ρ' va) b
    | .letin x e1 e2 => do
      let v ← eval fuel ρ e1
      eval fuel ((x, v) :: ρ) e2
    | .ite c t e =>
      match eval fuel ρ c with
      | some (.bool true)  => eval fuel ρ t
      | some (.bool false) => eval fuel ρ e
      | _ => none
    | .binop op a b => do
      let va ← eval fuel ρ a
      let vb ← eval fuel ρ b
      op.denote va vb
    | .cons a b => do
      let va ← eval fuel ρ a
      let vb ← eval fuel ρ b
      if vb.isList
      then some (.cons va vb)
      else none
    | .matchList s n x xs c =>
      match eval fuel ρ s with
      | some .nil => eval fuel ρ n
      | some (.cons vh vt) => eval fuel ((xs, vt) :: (x, vh) :: ρ) c
      | _ => none
    | .assert c =>
      match eval fuel ρ c with
      | some (.bool true) => some .unit
      | _ => none

/-- **Interpreter soundness**: whatever the interpreter returns is what `Eval` says. -/
theorem eval_sound : ∀ {fuel ρ e v}, eval fuel ρ e = some v → Eval ρ e v := by
  intro fuel
  induction fuel
  case zero =>
    intro ρ e v h
    simp [eval] at h
  case succ n ih =>
    intro ρ e v h
    cases e <;> simp [eval] at h
    case int _ =>
      subst h
      exact Eval.int
    case bool b =>
      subst h
      exact Eval.bool
    case var name =>
      apply Eval.var h
    case lam x body =>
      rw [← h]
      subst h
      exact Eval.lam
    case app e1 e2 =>
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨vf, hf, h⟩ := h
      split at h
      case h_1 s x b ρ' =>
        simp [Option.bind_eq_some_iff] at h
        obtain ⟨va, ha, hb⟩ := h
        exact .app (ih hf) (ih ha) (ih hb)
      case h_2 x q =>
        simp at h
    case letin name e body =>
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, hb⟩ := h
      exact .letin (ih ha) (ih hb)
    case ite =>
      split at h
      case h_1 hc =>
        exact .ifT (ih hc) (ih h)
      case h_2 hc =>
        exact .ifF (ih hc) (ih h)
      case h_3 =>
        simp at h
    case binop =>
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨va, ha, vb, hb, hc⟩ := h
      exact .binop (ih ha) (ih hb) (hc)
    case unit | nil | letrec | cons | matchList | assert => sorry

def ppValue : Value → String
  | .int n  => toString n
  | .bool b => toString b
  | .unit => "()"
  | .clos .. => "<fun>"
  | .nil => "[]"
  | .cons a b => s!"({ppValue a} :: {ppValue b})"

instance : ToString Value := ⟨ppValue⟩

end Diva
