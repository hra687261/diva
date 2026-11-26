import Diva.Opt
import Diva.AbsInt.MayFail

/-!
# Correctness of the optimiser

A program and its optimised version give related outcomes and related stores.
Related values are equal, except closures: the optimised closure's body is the
optimised body (`opt` rewrites under `fun`), so the relation is not equality.

The optimiser adds and removes no allocation, so addresses stay the same.

The proof has two parts, both by induction on `Eval`. Forward (`sim_fwd`): if the
source program gives an outcome, the optimised program gives a related outcome.
Backward (`sim_bwd`): if the optimised program gives an outcome, the source program
gives a related outcome. An expression that is replaced by its value is pure: it
terminates and leaves the store unchanged.

Both parts are needed because a looping program has no `Eval` derivation. The
forward part alone would allow `opt` to make a looping program terminate.
CompCert and CakeML prove only the forward part, because their semantics also
describe programs that run forever.

TODO: switch to small step semantics or add fuel to `Eval`.
-/

namespace Diva.Opt

open AbsInt AbsDomain NumDomain

variable {A : Type} [NumDomain A] {E : Bool}

/-- After `assert c`, when `c` is `true`, narrowing `σ` by `c` still gives the real
    values of `ρ`. -/
theorem afterAssert_sound {σ : AEnv A} {ρ : Env} {μ μ' : Store} {e1 : Expr} {v : Value}
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (h : Eval ρ μ e1 (.ok v) μ') :
    (afterAssert σ e1).Describes ρ ∧ (afterAssert σ e1).Bound ρ := by
  cases e1
  case assert c =>
    cases h with
    | assert hc =>
      obtain ⟨σ', hs, hd⟩ := σ.assume_sound hσ hc
      simp only [afterAssert, hs, Option.getD_some]
      exact ⟨hd, AEnv.assume_bound hB hs⟩
  all_goals exact ⟨hσ, hB⟩

/-! ## The optimiser as a relation -/

mutual
/-- `e'` is an optimised version of `e`, in the abstract environment `σ`. `opt H E σ e`
    is one (`optimizes_opt`). Stating it as a relation lets the proofs use `cases` on
    the optimised expression. Either `e` is replaced by its value `c` (`fold`), or
    `if` is replaced by the branch that its condition selects (`iteT`, `iteF`), or
    an assertion that certainly holds is replaced by `()` (`assertT`), or
    with `E`, an assertion whose condition is a check is replaced by `()`
    (`assertErase`), or
    `let x = e1 in e2` is replaced by `e2`, when `e1` is pure, can't fail (or, with `E`,
    fails only fatally), and `x` isn't used in the optimised `e2` (`letDrop`), or
    `a op b` is replaced by one side, the other being a unit of `op` (`identR`,
    `identL`), or
    `e` keeps its shape and its sub-expressions are optimised (`step`). -/
inductive Optimizes (H : Hints A) (E : Bool) : AEnv A → Expr → Expr → Prop where
  | fold {σ e c} : constOf H σ e = some c → Optimizes H E σ e c
  | iteT {σ c t t' e} : constOf H σ c = some (.bool true) →
      Optimizes H E ((σ.assume c true).getD σ) t t' → Optimizes H E σ (.ite c t e) t'
  | iteF {σ c t e e'} : constOf H σ c = some (.bool false) →
      Optimizes H E ((σ.assume c false).getD σ) e e' → Optimizes H E σ (.ite c t e) e'
  | identR {σ op a a' b n} : op.rightUnit = some n → constOf H σ b = some (.int n) →
      mayFail H σ (.binop op a b) = false → Optimizes H E σ a a' →
      Optimizes H E σ (.binop op a b) a'
  | identL {σ op a b b' n} : op.leftUnit = some n → constOf H σ a = some (.int n) →
      mayFail H σ (.binop op a b) = false → Optimizes H E σ b b' →
      Optimizes H E σ (.binop op a b) b'
  | assertT {σ c} : constOf H σ c = some (.bool true) → Optimizes H E σ (.assert c) .unit
  | assertErase {σ c} : E = true → c.isCheck = true → Optimizes H E σ (.assert c) .unit
  | letDrop {σ x e1 e2 e2'} :
      e1.pure = true → (mayFail H σ e1 = false ∨ E = true ∧ e1.onlyFatal = true) →
      (freeNames [] e2').contains x = false →
      Optimizes H E ((x, aeval H σ e1) :: afterAssert σ e1) e2 e2' →
      Optimizes H E σ (.letin x e1 e2) e2'
  | step {σ e e'} : OptStep H E σ e e' → Optimizes H E σ e e'

/-- `e'` has the shape of `e`, and each sub-expression of `e'` is an optimised version
    of the matching sub-expression of `e`. -/
inductive OptStep (H : Hints A) (E : Bool) : AEnv A → Expr → Expr → Prop where
  | int {σ n} : OptStep H E σ (.int n) (.int n)
  | bool {σ b} : OptStep H E σ (.bool b) (.bool b)
  | unit {σ} : OptStep H E σ .unit .unit
  | nil {σ} : OptStep H E σ .nil .nil
  | var {σ x} : OptStep H E σ (.var x) (.var x)
  | lam {σ x b b'} :
      Optimizes H E (bodyEnv H σ none x b) b b' → OptStep H E σ (.lam x b) (.lam x b')
  | letrec {σ f x b b' e e'} :
      Optimizes H E (bodyEnv H σ (some f) x b) b b' →
      Optimizes H E ((f, letrecVal H σ f x b) :: σ) e e' →
      OptStep H E σ (.letrec f x b e) (.letrec f x b' e')
  | app {σ f f' a a'} :
      Optimizes H E σ f f' → Optimizes H E σ a a' → OptStep H E σ (.app f a) (.app f' a')
  | letin {σ x e1 e1' e2 e2'} :
      Optimizes H E σ e1 e1' → Optimizes H E ((x, aeval H σ e1) :: afterAssert σ e1) e2 e2' →
      OptStep H E σ (.letin x e1 e2) (.letin x e1' e2')
  | binop {σ op a a' b b'} :
      Optimizes H E σ a a' → Optimizes H E σ b b' →
      OptStep H E σ (.binop op a b) (.binop op a' b')
  | cons {σ a a' b b'} :
      Optimizes H E σ a a' → Optimizes H E σ b b' → OptStep H E σ (.cons a b) (.cons a' b')
  | ite {σ c c' t t' e e'} :
      Optimizes H E σ c c' → Optimizes H E ((σ.assume c true).getD σ) t t' →
      Optimizes H E ((σ.assume c false).getD σ) e e' →
      OptStep H E σ (.ite c t e) (.ite c' t' e')
  | matchList {σ s s' n n' x xs c c'} :
      Optimizes H E σ s s' → Optimizes H E σ n n' →
      Optimizes H E ((xs, (aeval H σ s).tails) :: (x, AVal.ofFlat (aeval H σ s).heads) :: σ)
        c c' →
      OptStep H E σ (.matchList s n x xs c) (.matchList s' n' x xs c')
  | assert {σ c c'} : Optimizes H E σ c c' → OptStep H E σ (.assert c) (.assert c')
  | alloc {σ site n n' v v'} :
      Optimizes H E σ n n' → Optimizes H E σ v v' →
      OptStep H E σ (.alloc site n v) (.alloc site n' v')
  | get {σ a a' i i'} :
      Optimizes H E σ a a' → Optimizes H E σ i i' → OptStep H E σ (.get a i) (.get a' i')
  | set {σ a a' i i' v v'} :
      Optimizes H E σ a a' → Optimizes H E σ i i' → Optimizes H E σ v v' →
      OptStep H E σ (.set a i v) (.set a' i' v')
  | len {σ a a'} : Optimizes H E σ a a' → OptStep H E σ (.len a) (.len a')
  | ref {σ site v v'} : Optimizes H E σ v v' → OptStep H E σ (.ref site v) (.ref site v')
  | deref {σ r r'} : Optimizes H E σ r r' → OptStep H E σ (.deref r) (.deref r')
  | assign {σ r r' v v'} :
      Optimizes H E σ r r' → Optimizes H E σ v v' → OptStep H E σ (.assign r v) (.assign r' v')
  | ctor {σ t v v'} : Optimizes H E σ v v' → OptStep H E σ (.ctor t v) (.ctor t v')
  | raise {σ v v'} : Optimizes H E σ v v' → OptStep H E σ (.raise v) (.raise v')
  | tryw {σ a a' k h h'} :
      Optimizes H E σ a a' → Optimizes H E ((k, AVal.top) :: σ) h h' →
      OptStep H E σ (.tryw a k h) (.tryw a' k h')
  | ctorCase {σ s s' t x h h' m m'} :
      Optimizes H E σ s s' → Optimizes H E ((x, AVal.top) :: σ) h h' → Optimizes H E σ m m' →
      OptStep H E σ (.ctorCase s t x h m) (.ctorCase s' t x h' m')
end

theorem isInt_true {H : Hints A} {σ : AEnv A} {e : Expr} {n : Int}
    (h : isInt H σ e n = true) : constOf H σ e = some (.int n) := by
  unfold isInt at h
  split at h
  next m hm =>
    simp only [beq_iff_eq] at h
    rw [hm, h]
  next => cases h

theorem rightIdentity_true {H : Hints A} {σ : AEnv A} {op : BinOp} {a b : Expr}
    (h : rightIdentity H σ op a b = true) :
    ∃ n, op.rightUnit = some n ∧ constOf H σ b = some (.int n) ∧
      mayFail H σ (.binop op a b) = false := by
  unfold rightIdentity at h
  split at h
  next n hu =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨n, hu, isInt_true h.2, h.1⟩
  next => cases h

theorem leftIdentity_true {H : Hints A} {σ : AEnv A} {op : BinOp} {a b : Expr}
    (h : leftIdentity H σ op a b = true) :
    ∃ n, op.leftUnit = some n ∧ constOf H σ a = some (.int n) ∧
      mayFail H σ (.binop op a b) = false := by
  unfold leftIdentity at h
  split at h
  next n hu =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨n, hu, isInt_true h.2, h.1⟩
  next => cases h

/-- `opt H E σ e` is an optimised version of `e`, when `constOf` gives `none` too. -/
theorem optimizes_of_none {H : Hints A} {σ : AEnv A} {e : Expr}
    (h : constOf H σ e = none → OptStep H E σ e (opt H E σ e)) :
    Optimizes H E σ e (opt H E σ e) := by
  cases hc : constOf H σ e
  case none => exact .step (h hc)
  case some c =>
    rw [opt.eq_def, hc]
    exact .fold hc

/-- `opt H E σ e` is an optimised version of `e`. -/
theorem optimizes_opt (H : Hints A) (e : Expr) : ∀ σ, Optimizes H E σ e (opt H E σ e) := by
  induction e with
  | int n => intro σ; exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .int
  | bool b => intro σ; exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .bool
  | unit => intro σ; exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .unit
  | nil => intro σ; exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .nil
  | var x => intro σ; exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .var
  | lam x b ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .lam (ih _)
  | letrec f x b e ihb ihe =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .letrec (ihb _) (ihe _)
  | app f a ihf iha =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .app (ihf _) (iha _)
  | letin x e1 e2 ih1 ih2 =>
    intro σ
    cases hc : constOf H σ (.letin x e1 e2)
    case some v =>
      rw [opt.eq_def, hc]
      exact .fold hc
    case none =>
      rw [opt.eq_def, hc]
      simp only
      split
      next hd =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hd
        exact .letDrop hd.1.1 hd.1.2 hd.2 (ih2 _)
      next => exact .step (.letin (ih1 _) (ih2 _))
  | ite c t e ihc iht ihe =>
    intro σ
    cases hc : constOf H σ (.ite c t e)
    case some v =>
      rw [opt.eq_def, hc]
      exact .fold hc
    case none =>
      rw [opt.eq_def, hc]
      simp only
      split
      next hct => exact .iteT hct (iht _)
      next hcf => exact .iteF hcf (ihe _)
      next => exact .step (.ite (ihc _) (iht _) (ihe _))
  | binop op a b iha ihb =>
    intro σ
    cases hc : constOf H σ (.binop op a b)
    case some v =>
      rw [opt.eq_def, hc]
      exact .fold hc
    case none =>
      rw [opt.eq_def, hc]
      simp only
      split
      next hr =>
        obtain ⟨n, hu, hb, hf⟩ := rightIdentity_true hr
        exact .identR hu hb hf (iha _)
      next =>
        split
        next hl =>
          obtain ⟨n, hu, ha, hf⟩ := leftIdentity_true hl
          exact .identL hu ha hf (ihb _)
        next => exact .step (.binop (iha _) (ihb _))
  | cons a b iha ihb =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .cons (iha _) (ihb _)
  | matchList s n x xs c ihs ihn ihc =>
    intro σ
    exact optimizes_of_none fun hc => by
      rw [opt.eq_def, hc]
      exact .matchList (ihs _) (ihn _) (ihc _)
  | assert c ih =>
    intro σ
    cases hc : constOf H σ (.assert c)
    case some v =>
      rw [opt.eq_def, hc]
      exact .fold hc
    case none =>
      rw [opt.eq_def, hc]
      simp only
      split
      next he =>
        simp only [Bool.and_eq_true] at he
        exact .assertErase he.1 he.2
      next =>
        split
        next hct => exact .assertT hct
        next => exact .step (.assert (ih _))
  | alloc site n v ihn ihv =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .alloc (ihn _) (ihv _)
  | get a i iha ihi =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .get (iha _) (ihi _)
  | set a i v iha ihi ihv =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .set (iha _) (ihi _) (ihv _)
  | len a ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .len (ih _)
  | ref site v ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .ref (ih _)
  | deref r ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .deref (ih _)
  | assign r v ihr ihv =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .assign (ihr _) (ihv _)
  | ctor t v ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .ctor (ih _)
  | raise v ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .raise (ih _)
  | tryw a k h iha ihh =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .tryw (iha _) (ihh _)
  | ctorCase s t x h m ihs ihh ihm =>
    intro σ
    exact optimizes_of_none fun hc => by
      rw [opt.eq_def, hc]
      exact .ctorCase (ihs _) (ihh _) (ihm _)

/-! ## Related values, outcomes and stores

"Related" means equal, except for closures. A closure of the optimised program holds
the optimised body, because `opt` also optimises inside `fun`. Two closures are
related when the second body is an optimised version of the first, and their
environments are related. Environments, errors, outcomes and stores are related
when the values they hold are related.
-/

/-- A source value and an optimised value that agree. -/
inductive VR (H : Hints A) (E : Bool) : Value → Value → Prop where
  | int {n : Int} : VR H E (.int n) (.int n)
  | bool {b : Bool} : VR H E (.bool b) (.bool b)
  | unit : VR H E .unit .unit
  | nil : VR H E .nil .nil
  | cons {a a' b b' : Value} : VR H E a a' → VR H E b b' → VR H E (.cons a b) (.cons a' b')
  | arr {l : Nat} : VR H E (.arr l) (.arr l)
  | ref {l : Nat} : VR H E (.ref l) (.ref l)
  | ctor {t : String} {a a' : Value} : VR H E a a' → VR H E (.ctor t a) (.ctor t a')
  -- the optimised closure has an optimised body, and an environment related on the
  -- names `N`. The free names of the optimised body are in `N`, or are its parameter
  -- `x`, or the name `f` of the function in `let rec f x = ...`. `σ` describes the
  -- source closure's environment.
  | clos {s : Option String} {x : String} {b b' : Expr} {ρ ρ' : Env} (σ : AEnv A)
      (N : List String) :
      (∀ y ∈ N, ∀ w w', ρ.lookup y = some w → ρ'.lookup y = some w' → VR H E w w') →
      (∀ y ∈ N, (ρ.lookup y).isSome = (ρ'.lookup y).isSome) →
      (∀ y ∈ freeNames [] b', y ∈ x :: (s.toList ++ N)) →
      σ.Describes ρ → σ.Bound ρ →
      Optimizes H E (bodyEnv H σ s x b) b b' →
      VR H E (.clos s x b ρ) (.clos s x b' ρ')

/-- Environments related on the names `N`: each name of `N` is bound in both or in
    neither, to related values. The other names don't matter. After `letDrop`, the
    source environment binds `x` and the optimised one doesn't, so `x` isn't in `N`. -/
def EnvRel (H : Hints A) (E : Bool) (N : List String) (ρ ρ' : Env) : Prop :=
  (∀ y ∈ N, ∀ w w', ρ.lookup y = some w → ρ'.lookup y = some w' → VR H E w w') ∧
  (∀ y ∈ N, (ρ.lookup y).isSome = (ρ'.lookup y).isSome)

/-- Related errors: related raised exceptions, or the same runtime error. -/
inductive ErrRel (H : Hints A) (E : Bool) : Err → Err → Prop where
  | exn {v v' : Value} : VR H E v v' → ErrRel H E (.exn v) (.exn v')
  | same {k : Err} : k.isExn = false → ErrRel H E k k

/-- Related outcomes: related values, or related errors. -/
inductive OutRel (H : Hints A) (E : Bool) : Outcome → Outcome → Prop where
  | ok {v v' : Value} : VR H E v v' → OutRel H E (.ok v) (.ok v')
  | err {k k' : Err} : ErrRel H E k k' → OutRel H E (.err k) (.err k')

/-- Related contents of one address: the same length, and related values. -/
def CellRel (H : Hints A) (E : Bool) (c c' : List Value) : Prop :=
  c.length = c'.length ∧ ∀ (i : Nat) v v', c[i]? = some v → c'[i]? = some v' → VR H E v v'

/-- Related stores: the same addresses, with related contents. -/
def StoreRel (H : Hints A) (E : Bool) (μ μ' : Store) : Prop :=
  μ.length = μ'.length ∧
  ∀ (l : Nat) (c c' : List Value), μ[l]? = some c → μ'[l]? = some c' → CellRel H E c c'

/-- Two programs without free variables are equivalent: each gives an outcome iff
    the other does, and the outcomes and final stores are related. -/
def Equiv (H : Hints A) (E : Bool) (e e' : Expr) : Prop :=
  (∀ r μ, Eval [] [] e r μ → ∃ r' μ', Eval [] [] e' r' μ' ∧ OutRel H E r r' ∧ StoreRel H E μ μ') ∧
  (∀ r' μ', Eval [] [] e' r' μ' → ∃ r μ, Eval [] [] e r μ ∧ OutRel H E r r' ∧ StoreRel H E μ μ')

/-! ## Related values -/

namespace VR

variable {H : Hints A} {v v' : Value}

/-- On integers, related means equal. -/
theorem int_eq {n : Int} (h : VR H E (.int n) v) : v = .int n := by
  cases h
  rfl

theorem isClos (h : VR H E v v') : v'.isClos = v.isClos := by
  cases h <;> rfl

theorem isBool (h : VR H E v v') : v'.isBool = v.isBool := by
  cases h <;> rfl

theorem isList (h : VR H E v v') : v'.isList = v.isList := by
  cases h <;> rfl

theorem isCtor (h : VR H E v v') : v'.isCtor = v.isCtor := by
  cases h <;> rfl

end VR

theorem ErrRel.isExn {H : Hints A} {k k' : Err} (h : ErrRel H E k k') : k'.isExn = k.isExn := by
  cases h
  case exn => rfl
  case same => rfl

/-! ## Related environments -/

namespace EnvRel

variable {H : Hints A} {N : List String} {ρ ρ' : Env}

theorem nil : EnvRel H E N [] [] := by
  constructor
  · intro y _ w w' hw
    simp [List.lookup] at hw
  · intro y _
    rfl

/-- On fewer names. -/
theorem mono {N' : List String} (hρ : EnvRel H E N ρ ρ') (h : ∀ y ∈ N', y ∈ N) :
    EnvRel H E N' ρ ρ' := by
  constructor
  · intro y hy
    exact hρ.1 y (h y hy)
  · intro y hy
    exact hρ.2 y (h y hy)

/-- `y` is not `x`, if `y` is in `N` and `x` isn't. -/
theorem beq_false {x y : String} (hx : x ∉ N) (hy : y ∈ N) : (y == x) = false := by
  simp only [beq_eq_false_iff_ne]
  intro h
  subst h
  exact hx hy

/-- A name bound in the source environment only, and not in `N`. -/
theorem drop {x : String} {v : Value} (hρ : EnvRel H E N ρ ρ') (hx : x ∉ N) :
    EnvRel H E N ((x, v) :: ρ) ρ' := by
  constructor
  · intro y hy
    simp only [List.lookup, beq_false hx hy]
    exact hρ.1 y hy
  · intro y hy
    simp only [List.lookup, beq_false hx hy]
    exact hρ.2 y hy

/-- `y` is in `N`, if it is in `x :: N` and is not `x`. -/
theorem mem_of_ne {x y : String} (hy : y ∈ x :: N) (hxy : ¬y = x) : y ∈ N := by
  cases hy with
  | head => exact absurd rfl hxy
  | tail _ h => exact h

theorem cons {x : String} {v v' : Value} (hρ : EnvRel H E N ρ ρ') (hv : VR H E v v') :
    EnvRel H E (x :: N) ((x, v) :: ρ) ((x, v') :: ρ') := by
  constructor
  · intro y hy w w' hw hw'
    by_cases hxy : y = x
    · subst hxy
      simp [List.lookup] at hw hw'
      subst hw
      subst hw'
      exact hv
    · have hne : (y == x) = false := by simpa using hxy
      simp only [List.lookup, hne] at hw hw'
      exact hρ.1 y (mem_of_ne hy hxy) w w' hw hw'
  · intro y hy
    by_cases hxy : y = x
    · subst hxy
      simp [List.lookup]
    · have hne : (y == x) = false := by simpa using hxy
      simp only [List.lookup, hne]
      exact hρ.2 y (mem_of_ne hy hxy)

/-- A name of `N` bound in the source environment is bound in the optimised one, to a
    related value. -/
theorem lookup_some {y : String} {w : Value} (hρ : EnvRel H E N ρ ρ') (hy : y ∈ N)
    (hw : ρ.lookup y = some w) : ∃ w', ρ'.lookup y = some w' ∧ VR H E w w' := by
  cases hw' : ρ'.lookup y
  case none =>
    have hs := hρ.2 y hy
    simp [hw, hw'] at hs
  case some w' => exact ⟨w', rfl, hρ.1 y hy w w' hw hw'⟩

/-- A name of `N` bound in the optimised environment is bound in the source one, to a
    related value. -/
theorem lookup_some' {y : String} {w' : Value} (hρ : EnvRel H E N ρ ρ') (hy : y ∈ N)
    (hw' : ρ'.lookup y = some w') : ∃ w, ρ.lookup y = some w ∧ VR H E w w' := by
  cases hw : ρ.lookup y
  case none =>
    have hs := hρ.2 y hy
    simp [hw, hw'] at hs
  case some w => exact ⟨w, rfl, hρ.1 y hy w w' hw hw'⟩

theorem lookup_none {y : String} (hρ : EnvRel H E N ρ ρ') (hy : y ∈ N)
    (h : ρ.lookup y = none) : ρ'.lookup y = none := by
  have hs := hρ.2 y hy
  rw [h] at hs
  cases hw' : ρ'.lookup y
  case none => rfl
  case some w' => simp [hw'] at hs

theorem lookup_none' {y : String} (hρ : EnvRel H E N ρ ρ') (hy : y ∈ N)
    (h : ρ'.lookup y = none) : ρ.lookup y = none := by
  have hs := hρ.2 y hy
  rw [h] at hs
  cases hw : ρ.lookup y
  case none => rfl
  case some w => simp [hw] at hs

/-- Related closures called on related arguments run their bodies in environments
    related on the parameter `x`, the name of the function (for `let rec`), and `N`. -/
theorem call {s : Option String} {x : String} {b b' : Expr} {σ : AEnv A} {va va' : Value}
    (hρ : EnvRel H E N ρ ρ') (hNb : ∀ y ∈ freeNames [] b', y ∈ x :: (s.toList ++ N))
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ)
    (hb : Optimizes H E (bodyEnv H σ s x b) b b') (hv : VR H E va va') :
    EnvRel H E (x :: (s.toList ++ N)) (callEnv s x b ρ va) (callEnv s x b' ρ' va') := by
  cases s
  case none => exact hρ.cons hv
  case some f => exact (hρ.cons (.clos σ N hρ.1 hρ.2 hNb hσ hB hb)).cons hv

end EnvRel

/-- The abstract environment of a closure's body, in `opt`, describes the
    environment of a call to the closure. -/
theorem describes_bodyEnv {H : Hints A} {σ : AEnv A} {ρ : Env} {s : Option String}
    {x : String} {b : Expr} {va : Value} (hσ : σ.Describes ρ) (hB : σ.Bound ρ) :
    (bodyEnv H σ s x b).Describes (callEnv s x b ρ va) := by
  cases s
  case none => exact hσ.cons (AVal.mem_top va)
  case some f => exact (hσ.cons (letrecVal_mem hσ hB)).cons (AVal.mem_top va)

theorem bound_bodyEnv {H : Hints A} {σ : AEnv A} {ρ : Env} {s : Option String}
    {x : String} {b : Expr} {va : Value} (hB : σ.Bound ρ) :
    (bodyEnv H σ s x b).Bound (callEnv s x b ρ va) := by
  cases s
  case none => exact hB.cons
  case some f => exact hB.cons.cons

/-! ## Related stores -/

namespace CellRel

variable {H : Hints A} {c c' : List Value}

theorem get! {n : Nat} (hc : CellRel H E c c') (hn : n < c.length) : VR H E c[n]! c'[n]! := by
  have hn' : n < c'.length := hc.1 ▸ hn
  rw [getElem!_pos c n hn, getElem!_pos c' n hn']
  exact hc.2 n _ _ (List.getElem?_eq_getElem hn) (List.getElem?_eq_getElem hn')

theorem replicate {v v' : Value} (n : Nat) (hv : VR H E v v') :
    CellRel H E (List.replicate n v) (List.replicate n v') := by
  constructor
  · simp
  · intro i w w' hw hw'
    simp [List.getElem?_replicate] at hw hw'
    rw [← hw.2, ← hw'.2]
    exact hv

theorem single {v v' : Value} (hv : VR H E v v') : CellRel H E [v] [v'] :=
  CellRel.replicate 1 hv

theorem set {v v' : Value} (hc : CellRel H E c c') (i : Nat) (hv : VR H E v v') :
    CellRel H E (c.set i v) (c'.set i v') := by
  constructor
  · simp [hc.1]
  · intro j w w' hw hw'
    rw [List.getElem?_set] at hw hw'
    by_cases hij : i = j
    · simp [hij] at hw hw'
      rw [← hw.2, ← hw'.2]
      exact hv
    · simp only [hij, ↓reduceIte] at hw hw'
      exact hc.2 j w w' hw hw'

end CellRel

theorem eq_of_singleton {α : Type} {a b : α} {k : Nat} (h : [a][k]? = some b) : a = b := by
  cases k
  case zero => simpa using h
  case succ k => simp at h

namespace StoreRel

variable {H : Hints A} {μ μ' : Store}

theorem nil : StoreRel H E [] [] := by
  constructor
  · rfl
  · intro l c c' hc
    simp at hc

/-- An address holds contents in both stores, or in neither. The contents are
    related. -/
theorem get (hμ : StoreRel H E μ μ') (l : Nat) :
    (μ[l]? = none ∧ μ'[l]? = none) ∨
    ∃ c c', μ[l]? = some c ∧ μ'[l]? = some c' ∧ CellRel H E c c' := by
  have hlen := hμ.1
  by_cases hl : l < μ.length
  · right
    have hl' : l < μ'.length := by omega
    exact ⟨_, _, List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hl',
      hμ.2 l _ _ (List.getElem?_eq_getElem hl) (List.getElem?_eq_getElem hl')⟩
  · left
    constructor
    · simp only [List.getElem?_eq_none_iff]
      omega
    · simp only [List.getElem?_eq_none_iff]
      omega

theorem append {c c' : List Value} (hμ : StoreRel H E μ μ') (hc : CellRel H E c c') :
    StoreRel H E (μ ++ [c]) (μ' ++ [c']) := by
  have hlen := hμ.1
  constructor
  · simp [hlen]
  · intro l d d' hd hd'
    by_cases hl : l < μ.length
    · rw [List.getElem?_append_left hl] at hd
      rw [List.getElem?_append_left (by omega)] at hd'
      exact hμ.2 l d d' hd hd'
    · rw [List.getElem?_append_right (by omega)] at hd
      rw [List.getElem?_append_right (by omega)] at hd'
      rw [← eq_of_singleton hd, ← eq_of_singleton hd']
      exact hc

theorem set {c c' : List Value} (hμ : StoreRel H E μ μ') (l : Nat) (hc : CellRel H E c c') :
    StoreRel H E (μ.set l c) (μ'.set l c') := by
  constructor
  · simp [hμ.1]
  · intro m d d' hd hd'
    rw [List.getElem?_set] at hd hd'
    by_cases hlm : l = m
    · simp [hlm] at hd hd'
      rw [← hd.2, ← hd'.2]
      exact hc
    · simp only [hlm, ↓reduceIte] at hd hd'
      exact hμ.2 m d d' hd hd'

end StoreRel

/-! ## Operations on related values -/

section Ops

variable {H : Hints A} {μ μ' : Store}

theorem allocV_rel {vn vn' vv vv' : Value} (hμ : StoreRel H E μ μ') (hn : VR H E vn vn')
    (hv : VR H E vv vv') :
    OutRel H E (allocV μ vn vv).1 (allocV μ' vn' vv').1 ∧
    StoreRel H E (allocV μ vn vv).2 (allocV μ' vn' vv').2 := by
  cases hn
  case int n =>
    by_cases hneg : n < 0
    · simp only [allocV, hneg, ↓reduceIte]
      exact ⟨.err (.same rfl), hμ⟩
    · simp only [allocV, hneg, ↓reduceIte]
      rw [hμ.1]
      exact ⟨.ok .arr, hμ.append (CellRel.replicate _ hv)⟩
  -- not an integer: a type error, and the store doesn't change
  all_goals exact ⟨.err (.same rfl), hμ⟩

theorem getV_rel {va va' vi vi' : Value} (hμ : StoreRel H E μ μ') (ha : VR H E va va')
    (hi : VR H E vi vi') : OutRel H E (getV μ va vi) (getV μ' va' vi') := by
  cases ha
  case arr l =>
    cases hi
    case int i =>
      rcases hμ.get l with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
      · simp only [getV, h1, h2]
        exact .err (.same rfl)
      · simp only [getV, h1, h2, ← hc.1]
        by_cases hb : 0 ≤ i ∧ i < c.length
        · simp only [ite_eq_left hb]
          exact .ok (hc.get! (by omega))
        · simp only [ite_eq_right hb]
          exact .err (.same rfl)
    all_goals exact .err (.same rfl)
  all_goals exact .err (.same rfl)

theorem setV_rel {va va' vi vi' vv vv' : Value} (hμ : StoreRel H E μ μ') (ha : VR H E va va')
    (hi : VR H E vi vi') (hv : VR H E vv vv') :
    OutRel H E (setV μ va vi vv).1 (setV μ' va' vi' vv').1 ∧
    StoreRel H E (setV μ va vi vv).2 (setV μ' va' vi' vv').2 := by
  cases ha
  case arr l =>
    cases hi
    case int i =>
      rcases hμ.get l with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
      · simp only [setV, h1, h2]
        exact ⟨.err (.same rfl), hμ⟩
      · simp only [setV, h1, h2, ← hc.1]
        by_cases hb : 0 ≤ i ∧ i < c.length
        · simp only [ite_eq_left hb]
          exact ⟨.ok .unit, hμ.set l (hc.set i.toNat hv)⟩
        · simp only [ite_eq_right hb]
          exact ⟨.err (.same rfl), hμ⟩
    all_goals exact ⟨.err (.same rfl), hμ⟩
  all_goals exact ⟨.err (.same rfl), hμ⟩

theorem lenV_rel {va va' : Value} (hμ : StoreRel H E μ μ') (ha : VR H E va va') :
    OutRel H E (lenV μ va) (lenV μ' va') := by
  cases ha
  case arr l =>
    rcases hμ.get l with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
    · simp only [lenV, h1, h2]
      exact .err (.same rfl)
    · simp only [lenV, h1, h2, hc.1]
      exact .ok .int
  all_goals exact .err (.same rfl)

theorem refV_rel {v v' : Value} (hμ : StoreRel H E μ μ') (hv : VR H E v v') :
    OutRel H E (refV μ v).1 (refV μ' v').1 ∧ StoreRel H E (refV μ v).2 (refV μ' v').2 := by
  simp only [refV]
  rw [hμ.1]
  exact ⟨.ok .ref, hμ.append (CellRel.single hv)⟩

theorem derefV_rel {vr vr' : Value} (hμ : StoreRel H E μ μ') (hr : VR H E vr vr') :
    OutRel H E (derefV μ vr) (derefV μ' vr') := by
  cases hr
  case ref l =>
    rcases hμ.get l with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
    · simp only [derefV, h1, h2]
      exact .err (.same rfl)
    · have hlen := hc.1
      cases c with
      | nil =>
        cases c' with
        | nil =>
          simp only [derefV, h1, h2]
          exact .err (.same rfl)
        | cons w' ws' => simp at hlen
      | cons w ws =>
        cases c' with
        | nil => simp at hlen
        | cons w' ws' =>
          simp only [derefV, h1, h2]
          exact .ok (hc.2 0 w w' rfl rfl)
  all_goals exact .err (.same rfl)

theorem assignV_rel {vr vr' v v' : Value} (hμ : StoreRel H E μ μ') (hr : VR H E vr vr')
    (hv : VR H E v v') :
    OutRel H E (assignV μ vr v).1 (assignV μ' vr' v').1 ∧
    StoreRel H E (assignV μ vr v).2 (assignV μ' vr' v').2 := by
  cases hr
  case ref l =>
    rcases hμ.get l with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
    · simp only [assignV, h1, h2]
      exact ⟨.err (.same rfl), hμ⟩
    · simp only [assignV, h1, h2]
      exact ⟨.ok .unit, hμ.set l (CellRel.single hv)⟩
  all_goals exact ⟨.err (.same rfl), hμ⟩

/-- A binary operator gives an integer or a boolean. -/
theorem denote_ok_plain {op : BinOp} {va vb v : Value} (h : op.denote va vb = .ok v) :
    (∃ n, v = .int n) ∨ ∃ b, v = .bool b := by
  unfold BinOp.denote at h
  split at h
  -- `/` and `mod` have one more case: division by zero
  all_goals try split at h
  all_goals cases h
  all_goals simp

/-- A binary operator raises no exception. -/
theorem denote_err_plain {op : BinOp} {va vb : Value} {k : Err} (h : op.denote va vb = .err k) :
    k.isExn = false := by
  unfold BinOp.denote at h
  split at h
  all_goals try split at h
  all_goals cases h
  all_goals rfl

/-- The outcome of a binary operator is related to itself: it has no closure. -/
theorem denote_self (H : Hints A) (op : BinOp) (va vb : Value) :
    OutRel H E (op.denote va vb) (op.denote va vb) := by
  cases h : op.denote va vb with
  | ok v =>
    rcases denote_ok_plain h with ⟨n, rfl⟩ | ⟨b, rfl⟩
    · exact .ok .int
    · exact .ok .bool
  | err k => exact .err (.same (denote_err_plain h))

/-- A binary operator looks only at integers, booleans and `()`, on which related
    values are equal. -/
theorem denote_eq {op : BinOp} {va va' vb vb' : Value} (ha : VR H E va va') (hb : VR H E vb vb') :
    op.denote va' vb' = op.denote va vb := by
  cases ha <;> cases hb <;> cases op <;> rfl

theorem denote_rel {op : BinOp} {va va' vb vb' : Value} (ha : VR H E va va') (hb : VR H E vb vb') :
    OutRel H E (op.denote va vb) (op.denote va' vb') := by
  rw [denote_eq ha hb]
  exact denote_self H op va vb

end Ops

/-! ## Pure expressions -/

theorem bool_of_isBool {v : Value} (h : v.isBool = true) : ∃ b, v = .bool b := by
  cases v
  case bool b => exact ⟨b, rfl⟩
  all_goals simp [Value.isBool] at h

theorem list_of_isList {v : Value} (h : v.isList = true) :
    v = .nil ∨ ∃ a b, v = .cons a b := by
  cases v
  case nil => exact .inl rfl
  case cons a b => exact .inr ⟨a, b, rfl⟩
  all_goals simp [Value.isList] at h

theorem ctor_of_isCtor {v : Value} (h : v.isCtor = true) : ∃ t w, v = .ctor t w := by
  cases v
  case ctor t w => exact ⟨t, w, rfl⟩
  all_goals simp [Value.isCtor] at h

theorem exn_of_err_isExn {k : Err} (h : k.isExn = true) : ∃ w, k = .exn w := by
  cases k
  case exn w => exact ⟨w, rfl⟩
  all_goals simp [Err.isExn] at h

/-- A pure expression leaves the store as it found it. -/
theorem pure_store {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) : e.pure = true → μ₁ = μ := by
  induction h with
  | int | bool | unit | nil | var | varErr | lam => intro _; rfl
  | letrec _ ih => intro hi; exact ih hi
  | app | appNotFn | appErrF | appErrA | alloc | allocErrN | allocErrV
  | set | setErrA | setErrI | setErrV | ref | refErr | assign | assignErrR | assignErrV =>
    intro hi
    simp [Expr.pure] at hi
  | letin _ _ ih1 ih2 =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [ih2 hi.2, ih1 hi.1]
  | letinErr _ ih =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    exact ih hi.1
  | ifT _ _ ihc iht =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [iht hi.1.2, ihc hi.1.1]
  | ifF _ _ ihc ihe =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [ihe hi.2, ihc hi.1.1]
  | ifNotBool _ _ ihc | ifErr _ ihc | matchNotList _ _ ihc | matchErr _ ihc
  | ctorCaseNotCtor _ _ ihc | ctorCaseErr _ ihc =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    exact ihc hi.1.1
  | binop _ _ iha ihb | binopErrR _ _ iha ihb | cons _ _ _ iha ihb
  | consNotList _ _ _ iha ihb | consErrR _ _ iha ihb | get _ _ iha ihb
  | getErrI _ _ iha ihb | tryCatch _ _ iha ihb =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [ihb hi.2, iha hi.1]
  | binopErrL _ iha | consErrL _ iha | getErrA _ iha | tryOk _ iha | tryErr _ _ iha =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    exact iha hi.1
  | matchNil _ _ ihs ihn | ctorHit _ _ ihs ihn =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [ihn hi.1.2, ihs hi.1.1]
  | matchCons _ _ ihs ihc | ctorMiss _ _ _ ihs ihc =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [ihc hi.2, ihs hi.1.1]
  | assert _ ih | assertF _ ih | assertNotBool _ _ ih | assertErr _ ih | len _ ih
  | lenErr _ ih | deref _ ih | derefErr _ ih | ctor _ ih | ctorErr _ ih | raise _ _ ih
  | raiseNotCtor _ _ ih | raiseErr _ ih =>
    intro hi
    exact ih hi

/-- A pure expression terminates: it contains no call, so it can't loop. -/
theorem pure_total (e : Expr) : e.pure = true → ∀ ρ μ, ∃ r μ₁, Eval ρ μ e r μ₁ := by
  induction e with
  | int n => intro _ ρ μ; exact ⟨_, _, .int⟩
  | bool b => intro _ ρ μ; exact ⟨_, _, .bool⟩
  | unit => intro _ ρ μ; exact ⟨_, _, .unit⟩
  | nil => intro _ ρ μ; exact ⟨_, _, .nil⟩
  | lam x b => intro _ ρ μ; exact ⟨_, _, .lam⟩
  | var x =>
    intro _ ρ μ
    cases hx : ρ.lookup x
    case none => exact ⟨_, _, .varErr hx⟩
    case some v => exact ⟨_, _, .var hx⟩
  | app | alloc | set | ref | assign =>
    intro hi
    simp [Expr.pure] at hi
  | letrec f x b e2 _ ih =>
    intro hi ρ μ
    obtain ⟨r, μ₁, h⟩ := ih hi _ μ
    exact ⟨_, _, .letrec h⟩
  | letin x e1 e2 ih1 ih2 =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨r1, μ₁, h1⟩ := ih1 hi.1 ρ μ
    cases r1 with
    | err k => exact ⟨_, _, .letinErr h1⟩
    | ok v1 =>
      obtain ⟨r, μ₂, h2⟩ := ih2 hi.2 ((x, v1) :: ρ) μ₁
      exact ⟨_, _, .letin h1 h2⟩
  | ite c t e ihc iht ihe =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨rc, μ₁, hc⟩ := ihc hi.1.1 ρ μ
    cases rc with
    | err k => exact ⟨_, _, .ifErr hc⟩
    | ok v =>
      cases hb : v.isBool
      case false => exact ⟨_, _, .ifNotBool hc hb⟩
      case true =>
        obtain ⟨b, rfl⟩ := bool_of_isBool hb
        cases b
        case true =>
          obtain ⟨r, μ₂, ht⟩ := iht hi.1.2 ρ μ₁
          exact ⟨_, _, .ifT hc ht⟩
        case false =>
          obtain ⟨r, μ₂, he⟩ := ihe hi.2 ρ μ₁
          exact ⟨_, _, .ifF hc he⟩
  | binop op a b iha ihb =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨ra, μ₁, ha⟩ := iha hi.1 ρ μ
    cases ra with
    | err k => exact ⟨_, _, .binopErrL ha⟩
    | ok va =>
      obtain ⟨rb, μ₂, hb⟩ := ihb hi.2 ρ μ₁
      cases rb with
      | err k => exact ⟨_, _, .binopErrR ha hb⟩
      | ok vb => exact ⟨_, _, .binop ha hb⟩
  | cons a b iha ihb =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨ra, μ₁, ha⟩ := iha hi.1 ρ μ
    cases ra with
    | err k => exact ⟨_, _, .consErrL ha⟩
    | ok va =>
      obtain ⟨rb, μ₂, hb⟩ := ihb hi.2 ρ μ₁
      cases rb with
      | err k => exact ⟨_, _, .consErrR ha hb⟩
      | ok vb =>
        cases hl : vb.isList
        case true => exact ⟨_, _, .cons ha hb hl⟩
        case false => exact ⟨_, _, .consNotList ha hb hl⟩
  | matchList s n x xs c ihs ihn ihc =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨rs, μ₁, hs⟩ := ihs hi.1.1 ρ μ
    cases rs with
    | err k => exact ⟨_, _, .matchErr hs⟩
    | ok v =>
      cases hl : v.isList
      case false => exact ⟨_, _, .matchNotList hs hl⟩
      case true =>
        rcases list_of_isList hl with rfl | ⟨vh, vt, rfl⟩
        · obtain ⟨r, μ₂, hn⟩ := ihn hi.1.2 ρ μ₁
          exact ⟨_, _, .matchNil hs hn⟩
        · obtain ⟨r, μ₂, hc⟩ := ihc hi.2 ((xs, vt) :: (x, vh) :: ρ) μ₁
          exact ⟨_, _, .matchCons hs hc⟩
  | assert c ih =>
    intro hi ρ μ
    obtain ⟨rc, μ₁, hc⟩ := ih hi ρ μ
    cases rc with
    | err k => exact ⟨_, _, .assertErr hc⟩
    | ok v =>
      cases hb : v.isBool
      case false => exact ⟨_, _, .assertNotBool hc hb⟩
      case true =>
        obtain ⟨b, rfl⟩ := bool_of_isBool hb
        cases b
        case true => exact ⟨_, _, .assert hc⟩
        case false => exact ⟨_, _, .assertF hc⟩
  | get a i iha ihi =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨ra, μ₁, ha⟩ := iha hi.1 ρ μ
    cases ra with
    | err k => exact ⟨_, _, .getErrA ha⟩
    | ok va =>
      obtain ⟨ri, μ₂, hi'⟩ := ihi hi.2 ρ μ₁
      cases ri with
      | err k => exact ⟨_, _, .getErrI ha hi'⟩
      | ok vi => exact ⟨_, _, .get ha hi'⟩
  | len a ih =>
    intro hi ρ μ
    obtain ⟨ra, μ₁, ha⟩ := ih hi ρ μ
    cases ra with
    | err k => exact ⟨_, _, .lenErr ha⟩
    | ok va => exact ⟨_, _, .len ha⟩
  | deref r ih =>
    intro hi ρ μ
    obtain ⟨rr, μ₁, hr⟩ := ih hi ρ μ
    cases rr with
    | err k => exact ⟨_, _, .derefErr hr⟩
    | ok vr => exact ⟨_, _, .deref hr⟩
  | ctor t v ih =>
    intro hi ρ μ
    obtain ⟨rv, μ₁, hv⟩ := ih hi ρ μ
    cases rv with
    | err k => exact ⟨_, _, .ctorErr hv⟩
    | ok w => exact ⟨_, _, .ctor hv⟩
  | raise v ih =>
    intro hi ρ μ
    obtain ⟨rv, μ₁, hv⟩ := ih hi ρ μ
    cases rv with
    | err k => exact ⟨_, _, .raiseErr hv⟩
    | ok w =>
      cases hx : w.isCtor
      case true => exact ⟨_, _, .raise hv hx⟩
      case false => exact ⟨_, _, .raiseNotCtor hv hx⟩
  | tryw a k h iha ihh =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨ra, μ₁, ha⟩ := iha hi.1 ρ μ
    cases ra with
    | ok v => exact ⟨_, _, .tryOk ha⟩
    | err kr =>
      cases hx : kr.isExn
      case false => exact ⟨_, _, .tryErr ha hx⟩
      case true =>
        obtain ⟨w, rfl⟩ := exn_of_err_isExn hx
        obtain ⟨r, μ₂, hh⟩ := ihh hi.2 ((k, w) :: ρ) μ₁
        exact ⟨_, _, .tryCatch ha hh⟩
  | ctorCase s t x h m ihs ihh ihm =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨rs, μ₁, hs⟩ := ihs hi.1.1 ρ μ
    cases rs with
    | err k => exact ⟨_, _, .ctorCaseErr hs⟩
    | ok v =>
      cases hx : v.isCtor
      case false => exact ⟨_, _, .ctorCaseNotCtor hs hx⟩
      case true =>
        obtain ⟨t', w, rfl⟩ := ctor_of_isCtor hx
        by_cases ht : t' = t
        · subst ht
          obtain ⟨r, μ₂, hh⟩ := ihh hi.1.2 ((x, w) :: ρ) μ₁
          exact ⟨_, _, .ctorHit hs hh⟩
        · obtain ⟨r, μ₂, hm⟩ := ihm hi.2 ρ μ₁
          exact ⟨_, _, .ctorMiss hs ht hm⟩

/-! ## Folded expressions -/

/-- `a` has no summary and no elements, so the values it describes are those of its
    flags and integers. -/
theorem flat_of_mem {a : AVal A} {v : Value} (hse : ¬ (a.sum.isSome || a.elems.isSome) = true)
    (hv : a.mem v) : a.toFlat.mem v := by
  cases hv with
  | flat h => exact h
  | sum _ _ hS => simp [hS] at hse
  | list hE _ _ => simp [hE] at hse

/-- If `literal a` is `c`, every value `a` describes is the value of `c`. -/
theorem literal_sound {a : AVal A} {c : Expr} {v : Value} (hl : literal a = some c)
    (hv : a.mem v) : (∃ n, c = .int n ∧ v = .int n) ∨ (∃ b, c = .bool b ∧ v = .bool b) := by
  unfold literal at hl
  split at hl
  case isTrue => cases hl
  case isFalse hse =>
    have hf : a.toFlat.mem v := flat_of_mem hse hv
    split at hl
    case h_1 n hn =>
      split at hl
      case isTrue hle =>
        cases hl
        -- `v` is an integer described by `a.int`, which describes only `n`
        have hi : (Flat.ofInt a.int).mem v := Flat.mem_leq hf hle
        cases v
        case int m =>
          have hm : m = n := asConst_sound hn hi
          exact .inl ⟨n, rfl, by rw [hm]⟩
        case bool b => cases b <;> simp [Flat.mem, Flat.ofInt, Flat.bot] at hi
        all_goals simp [Flat.mem, Flat.ofInt, Flat.bot] at hi
      case isFalse => cases hl
    case h_2 =>
      split at hl
      case isTrue hle =>
        cases hl
        simp only [Bool.and_eq_true] at hle
        -- `v` is a boolean that may only be `true`
        have hb : (Flat.bools true false : Flat A).mem v := Flat.mem_leq hf hle.1
        cases v
        case int m => exact absurd hb (bot_sound m)
        case bool b =>
          cases b
          case true => exact .inr ⟨true, rfl, rfl⟩
          case false => simp [Flat.mem, Flat.bools, Flat.bot] at hb
        all_goals simp [Flat.mem, Flat.bools, Flat.bot] at hb
      case isFalse =>
        split at hl
        case isTrue hle =>
          cases hl
          simp only [Bool.and_eq_true] at hle
          have hb : (Flat.bools false true : Flat A).mem v := Flat.mem_leq hf hle.1
          cases v
          case int m => exact absurd hb (bot_sound m)
          case bool b =>
            cases b
            case true => simp [Flat.mem, Flat.bools, Flat.bot] at hb
            case false => exact .inr ⟨false, rfl, rfl⟩
          all_goals simp [Flat.mem, Flat.bools, Flat.bot] at hb
        case isFalse => cases hl

theorem constOf_some {H : Hints A} {σ : AEnv A} {e c : Expr} (h : constOf H σ e = some c) :
    e.pure = true ∧ mayFail H σ e = false ∧ literal (aeval H σ e) = some c := by
  unfold constOf at h
  split at h
  case isTrue hc =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact ⟨hc.1, hc.2, h⟩
  case isFalse => cases h

/-- Forward, for an expression replaced by the literal `c`: `e` gives the value of
    `c`, and doesn't change the store. -/
theorem fold_fwd {H : Hints A} {σ : AEnv A} {e c : Expr} {ρ ρ' : Env} {μ μ₁ μ' : Store}
    {r : Outcome} (hc : constOf H σ e = some c) (hσ : σ.Describes ρ) (hB : σ.Bound ρ)
    (h : Eval ρ μ e r μ₁) (hμ : StoreRel H E μ μ') :
    ∃ r' μ₁', Eval ρ' μ' c r' μ₁' ∧ OutRel H E r r' ∧ StoreRel H E μ₁ μ₁' := by
  obtain ⟨hi, hf, hl⟩ := constOf_some hc
  rw [pure_store h hi]
  cases r with
  | err k =>
    -- `mayFail` said that `e` can't fail
    have hm := mayFail_sound (H := H) hσ hB h
    rw [hf] at hm
    cases hm
  | ok v =>
    rcases literal_sound hl (aeval_sound hσ hB h) with ⟨n, rfl, rfl⟩ | ⟨b, rfl, rfl⟩
    · exact ⟨_, _, .int, .ok .int, hμ⟩
    · exact ⟨_, _, .bool, .ok .bool, hμ⟩

/-- Backward, for an expression replaced by the literal `c`: `e` terminates, gives
    the value of `c`, and doesn't change the store. -/
theorem fold_bwd {H : Hints A} {σ : AEnv A} {e c : Expr} {ρ ρ' : Env} {μ μ' μ₁' : Store}
    {r' : Outcome} (hc : constOf H σ e = some c) (hσ : σ.Describes ρ) (hB : σ.Bound ρ)
    (h' : Eval ρ' μ' c r' μ₁') (hμ : StoreRel H E μ μ') :
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H E r r' ∧ StoreRel H E μ₁ μ₁' := by
  obtain ⟨hi, hf, hl⟩ := constOf_some hc
  obtain ⟨r, μ₁, h⟩ := pure_total e hi ρ μ
  have hμ₁ := pure_store h hi
  subst hμ₁
  cases r with
  | err k =>
    have hm := mayFail_sound (H := H) hσ hB h
    rw [hf] at hm
    cases hm
  | ok v =>
    rcases literal_sound hl (aeval_sound hσ hB h) with ⟨n, rfl, rfl⟩ | ⟨b, rfl, rfl⟩
    · cases h'
      exact ⟨_, _, h, .ok .int, hμ⟩
    · cases h'
      exact ⟨_, _, h, .ok .bool, hμ⟩

/-- If `constOf` gives the boolean `b` for `c`, `c` gives `b` and doesn't change the
    store. -/
theorem constOf_bool {H : Hints A} {σ : AEnv A} {c : Expr} {b : Bool} {ρ : Env}
    {μ μ₁ : Store} {r : Outcome} (hc : constOf H σ c = some (.bool b))
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (h : Eval ρ μ c r μ₁) :
    r = .ok (.bool b) ∧ μ₁ = μ := by
  obtain ⟨hi, hf, hl⟩ := constOf_some hc
  cases r with
  | err k =>
    have hm := mayFail_sound (H := H) hσ hB h
    rw [hf] at hm
    cases hm
  | ok v =>
    rcases literal_sound hl (aeval_sound hσ hB h) with ⟨n, hn, _⟩ | ⟨b', hb, hv⟩
    · cases hn
    · cases hb
      rw [hv]
      exact ⟨rfl, pure_store h hi⟩

/-- If `constOf` gives the integer `n` for `c`, `c` gives `n` and doesn't change the
    store. -/
theorem constOf_int {H : Hints A} {σ : AEnv A} {c : Expr} {n : Int} {ρ : Env}
    {μ μ₁ : Store} {r : Outcome} (hc : constOf H σ c = some (.int n))
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (h : Eval ρ μ c r μ₁) :
    r = .ok (.int n) ∧ μ₁ = μ := by
  obtain ⟨hi, hf, hl⟩ := constOf_some hc
  cases r with
  | err k =>
    have hm := mayFail_sound (H := H) hσ hB h
    rw [hf] at hm
    cases hm
  | ok v =>
    rcases literal_sound hl (aeval_sound hσ hB h) with ⟨m, hm, hv⟩ | ⟨b, hb, _⟩
    · cases hm
      rw [hv]
      exact ⟨rfl, pure_store h hi⟩
    · cases hb

/-- `v op n`, with `n` the right unit of `op`, gives the value `w` only if `v` is
    `w`. -/
theorem denote_rightUnit_ok {op : BinOp} {n : Int} {v w : Value}
    (hu : op.rightUnit = some n) (h : op.denote v (.int n) = .ok w) : v = w := by
  cases op
  case add => cases hu; cases v <;> simp_all [BinOp.denote]
  case sub => cases hu; cases v <;> simp_all [BinOp.denote]
  case mul => cases hu; cases v <;> simp_all [BinOp.denote]
  case div => cases hu; cases v <;> simp_all [BinOp.denote]
  all_goals cases hu

/-- `n op v`, with `n` the left unit of `op`, gives the value `w` only if `v` is
    `w`. -/
theorem denote_leftUnit_ok {op : BinOp} {n : Int} {v w : Value}
    (hu : op.leftUnit = some n) (h : op.denote (.int n) v = .ok w) : v = w := by
  cases op
  case add => cases hu; cases v <;> simp_all [BinOp.denote]
  case mul => cases hu; cases v <;> simp_all [BinOp.denote]
  all_goals cases hu

/-- If `a op n` gives a value, with `n` the right unit of `op`, `a` gives that
    value. -/
theorem eval_identR {op : BinOp} {n : Int} {ρ : Env} {μ μ₁ : Store} {a : Expr}
    {w : Value} (hu : op.rightUnit = some n)
    (h : Eval ρ μ (.binop op a (.int n)) (.ok w) μ₁) : Eval ρ μ a (.ok w) μ₁ := by
  generalize hr : Outcome.ok w = r at h
  cases h with
  | binop ha hb =>
    cases hb
    rw [← hr, ← denote_rightUnit_ok hu hr.symm]
    exact ha
  | binopErrL _ => cases hr
  | binopErrR _ hb => cases hb

/-- If `n op b` gives a value, with `n` the left unit of `op`, `b` gives that
    value. -/
theorem eval_identL {op : BinOp} {n : Int} {ρ : Env} {μ μ₁ : Store} {b : Expr}
    {w : Value} (hu : op.leftUnit = some n)
    (h : Eval ρ μ (.binop op (.int n) b) (.ok w) μ₁) : Eval ρ μ b (.ok w) μ₁ := by
  generalize hr : Outcome.ok w = r at h
  cases h with
  | binop ha hb =>
    cases ha
    rw [← hr, ← denote_leftUnit_ok hu hr.symm]
    exact hb
  | binopErrL ha => cases ha
  | binopErrR _ _ => cases hr

/-- `if true then t else e` gives what `t` gives. -/
theorem eval_ite_true {ρ : Env} {μ μ₁ : Store} {t e : Expr} {r : Outcome}
    (h : Eval ρ μ (.ite (.bool true) t e) r μ₁) : Eval ρ μ t r μ₁ := by
  cases h with
  | ifT hc ht => cases hc; exact ht
  | ifF hc _ => cases hc
  | ifNotBool hc hv => cases hc; cases hv
  | ifErr hc => cases hc

/-- `if false then t else e` gives what `e` gives. -/
theorem eval_ite_false {ρ : Env} {μ μ₁ : Store} {t e : Expr} {r : Outcome}
    (h : Eval ρ μ (.ite (.bool false) t e) r μ₁) : Eval ρ μ e r μ₁ := by
  cases h with
  | ifT hc _ => cases hc
  | ifF hc he => cases hc; exact he
  | ifNotBool hc hv => cases hc; cases hv
  | ifErr hc => cases hc


/-! ## Checks -/

/-- A fatal error: an error that isn't an exception. No `try` catches it, so it ends
    the whole program. -/
def _root_.Diva.Outcome.fatal : Outcome → Prop
  | .ok _ => False
  | .err k => k.isExn = false

/-- An operator fails only with `divZero` or `typeError`, never with an exception. -/
theorem denote_err_not_exn {op : BinOp} {va vb : Value} {k : Err}
    (h : op.denote va vb = .err k) : k.isExn = false := by
  unfold BinOp.denote at h
  split at h
  all_goals grind [Err.isExn]

theorem isCheck_pure {e : Expr} (h : e.isCheck = true) : e.pure = true := by
  induction e with
  | binop op a b iha ihb =>
    simp only [Expr.isCheck, Bool.and_eq_true] at h
    simp [Expr.pure, iha h.1, ihb h.2]
  | ite c t e ihc iht ihe =>
    simp only [Expr.isCheck, Bool.and_eq_true] at h
    simp [Expr.pure, ihc h.1.1, iht h.1.2, ihe h.2]
  | int | bool | unit | var | nil => rfl
  | _ => simp [Expr.isCheck] at h

/-- A check fails only with errors that are not exceptions. -/
theorem isCheck_err {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) (hc : e.isCheck = true) : ¬ (∃ v, r = .err (.exn v)) := by
  induction h with
  | binop _ _ =>
    intro ⟨v, hv⟩
    have := denote_err_not_exn hv
    simp [Err.isExn] at this
  | binopErrL _ ih =>
    simp only [Expr.isCheck, Bool.and_eq_true] at hc
    exact ih hc.1
  | binopErrR _ _ _ ih =>
    simp only [Expr.isCheck, Bool.and_eq_true] at hc
    exact ih hc.2
  | ifT _ _ _ ih =>
    simp only [Expr.isCheck, Bool.and_eq_true] at hc
    exact ih hc.1.2
  | ifF _ _ _ ih =>
    simp only [Expr.isCheck, Bool.and_eq_true] at hc
    exact ih hc.2
  | ifErr _ ih =>
    simp only [Expr.isCheck, Bool.and_eq_true] at hc
    exact ih hc.1.1
  -- the other expressions are not checks
  | _ => simp_all [Expr.isCheck]

/-- An error of a check is fatal. -/
theorem isCheck_fatal {ρ : Env} {μ μ₁ : Store} {e : Expr} {k : Err}
    (h : Eval ρ μ e (.err k) μ₁) (hc : e.isCheck = true) : (Outcome.err k).fatal := by
  cases k with
  | exn v => exact absurd ⟨v, rfl⟩ (isCheck_err h hc)
  | _ => rfl

/-- An error of `assert c`, where `c` is a check, or of a check, is fatal. -/
theorem onlyFatal_fatal {ρ : Env} {μ μ₁ : Store} {e : Expr} {k : Err}
    (h : Eval ρ μ e (.err k) μ₁) (hc : e.onlyFatal = true) : (Outcome.err k).fatal := by
  cases e
  case assert c =>
    cases h with
    | assertF _ => rfl
    | assertNotBool _ _ => rfl
    | assertErr hce => exact isCheck_fatal hce hc
  all_goals exact isCheck_fatal h hc

/-! ## Forward: what the source program does, the optimised one does too -/

/-! The simulations have three hypotheses that each call would have to prove: `hN`
(the free names are in `N`), `hF` and `hS` (no fatal error). The tactics `fv_sub`,
`fatal_sub` and `safe_sub` prove them from the same hypotheses of the enclosing
expression, as automatic arguments (`:= by ...`), so the calls don't write them.
`set_option hygiene false` lets the tactics use the names `hN`, `hF` and `hS` of the
proof where they run: otherwise Lean renames the names written in a macro. -/

set_option hygiene false in
/-- Proves that the free names of an optimised expression are in `N`, the names on
    which its environments are related. It uses `hN`: the free names of the enclosing
    optimised expression are in the names of its environments. -/
macro "fv_sub" : tactic => `(tactic| first
  | assumption
  | exact fun _ h => h
  | (intro y hy
     have hy' := hN y
     simp only [freeNames, List.mem_append, mem_freeNames_cons, List.mem_cons,
       Option.toList, List.nil_append, List.cons_append, List.not_mem_nil] at hy hy' ⊢
     grind))

set_option hygiene false in
/-- Proves that the outcome of a sub-expression isn't fatal, from `hF`, which says the
    same of the enclosing expression: a fatal error would be its outcome too. -/
macro "fatal_sub" : tactic => `(tactic| first
  | assumption
  | (intro _ hf
     simp [Outcome.fatal, Err.isExn] at hf))

set_option hygiene false in
/-- Proves that no run of a sub-expression has a fatal error, from `hS`, which says the
    same of the enclosing expression: `solve_by_elim` builds the run of the enclosing
    expression that would end in that error. -/
macro "safe_sub" : tactic => `(tactic| first
  | assumption
  | (intro hE r₀ μ₀ h₀ hf₀
     cases r₀ with
     | ok v₀ => simp [Outcome.fatal] at hf₀
     | err k₀ =>
       simp only [Outcome.fatal] at hf₀
       exact hS hE (.err k₀) _ (by solve_by_elim (maxDepth := 4) [Eval.letrec, Eval.app,
         Eval.appErrF, Eval.appErrA, Eval.letin, Eval.letinErr, Eval.ifT, Eval.ifF,
         Eval.ifErr, Eval.binopErrL, Eval.binopErrR, Eval.consErrL, Eval.consErrR,
         Eval.matchNil, Eval.matchCons, Eval.matchErr, Eval.assertErr, Eval.allocErrN,
         Eval.allocErrV, Eval.getErrA, Eval.getErrI, Eval.setErrA, Eval.setErrI,
         Eval.setErrV, Eval.lenErr, Eval.refErr, Eval.derefErr, Eval.assignErrR,
         Eval.assignErrV, Eval.ctorErr, Eval.raiseErr, Eval.tryCatch, Eval.tryErr,
         Eval.ctorHit, Eval.ctorMiss, Eval.ctorCaseErr]) hf₀))

/-- `e` gives `r` in `ρ` and `μ`. Every `e'` related to `e` by `R`, run in an
    environment related on the free names of `e'`, and in a related store, gives an
    outcome related to `r`. -/
def FwdSim (H : Hints A) (E : Bool) (R : AEnv A → Expr → Expr → Prop) (ρ : Env) (μ : Store)
    (e : Expr) (r : Outcome) (μ₁ : Store) : Prop :=
  ∀ {σ : AEnv A} {e' : Expr} {ρ' : Env} {μ' : Store} {N : List String},
    σ.Describes ρ → σ.Bound ρ → R σ e e' → EnvRel H E N ρ ρ' → StoreRel H E μ μ' →
    (hN : ∀ y ∈ freeNames [] e', y ∈ N := by fv_sub) →
    (hF : E = true → ¬ r.fatal := by fatal_sub) →
    ∃ r' μ₁', Eval ρ' μ' e' r' μ₁' ∧ OutRel H E r r' ∧ StoreRel H E μ₁ μ₁'

/-- `OptStep`, and the cases of `Optimizes` that the forward simulation proves with the
    evaluation of a sub-expression of `e`: the branch kept by `iteT` or `iteF`, and `e2`
    in `letDrop`. -/
inductive FwdStep (H : Hints A) (E : Bool) : AEnv A → Expr → Expr → Prop where
  | step {σ e e'} : OptStep H E σ e e' → FwdStep H E σ e e'
  | iteT {σ c t t' e} : constOf H σ c = some (.bool true) →
      Optimizes H E ((σ.assume c true).getD σ) t t' → FwdStep H E σ (.ite c t e) t'
  | iteF {σ c t e e'} : constOf H σ c = some (.bool false) →
      Optimizes H E ((σ.assume c false).getD σ) e e' → FwdStep H E σ (.ite c t e) e'
  | letDrop {σ x e1 e2 e2'} :
      e1.pure = true → (mayFail H σ e1 = false ∨ E = true ∧ e1.onlyFatal = true) →
      (freeNames [] e2').contains x = false →
      Optimizes H E ((x, aeval H σ e1) :: afterAssert σ e1) e2 e2' →
      FwdStep H E σ (.letin x e1 e2) e2'

/-- Adds the cases of `fold`, `assertT`, `identR` and `identL` to the cases of
    `FwdStep`. -/
theorem lift_fwd {H : Hints A} {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) (ih : FwdSim H E (FwdStep H E) ρ μ e r μ₁) :
    FwdSim H E (Optimizes H E) ρ μ e r μ₁ := by
  intro σ e' ρ' μ' N hσ hB ho hρ hμ hN hF
  cases ho with
  | fold hc => exact fold_fwd hc hσ hB h hμ
  | iteT hc hot => exact ih hσ hB (.iteT hc hot) hρ hμ
  | iteF hc hoe => exact ih hσ hB (.iteF hc hoe) hρ hμ
  | letDrop hp hf hx ho2 => exact ih hσ hB (.letDrop hp hf hx ho2) hρ hμ
  | assertErase hE hc =>
    -- the source run has no fatal error, so `c` gives `true`. `c` doesn't change the store.
    cases h with
    | assert hce =>
      obtain rfl := pure_store hce (isCheck_pure hc)
      exact ⟨_, _, .unit, .ok .unit, hμ⟩
    | assertF hce => exact (hF hE rfl).elim
    | assertNotBool hce hv => exact (hF hE rfl).elim
    | assertErr hce => exact (hF hE (isCheck_fatal hce hc)).elim
  | assertT hc =>
    -- `c` gives `true` and doesn't change the store, so `assert c` gives `()`
    cases h with
    | assert hce =>
      obtain ⟨_, rfl⟩ := constOf_bool hc hσ hB hce
      exact ⟨_, _, .unit, .ok .unit, hμ⟩
    | assertF hce => cases (constOf_bool hc hσ hB hce).1
    | assertNotBool hce hv =>
      obtain ⟨heq, _⟩ := constOf_bool hc hσ hB hce
      cases heq
      cases hv
    | assertErr hce => cases (constOf_bool hc hσ hB hce).1
  | identR hu hb hf hoa =>
    -- `a' op n` is related to `e` by `OptStep`, and gives what `a'` gives
    obtain ⟨r', μ₁', h', hr, hμ₁⟩ := ih hσ hB (.step (.binop hoa (.fold hb))) hρ hμ
    cases hr with
    | ok hv => exact ⟨_, _, eval_identR hu h', .ok hv, hμ₁⟩
    | err _ =>
      -- `a op b` can't fail
      have hm := mayFail_sound (H := H) hσ hB h
      rw [hf] at hm
      cases hm
  | identL hu ha hf hob =>
    obtain ⟨r', μ₁', h', hr, hμ₁⟩ := ih hσ hB (.step (.binop (.fold ha) hob)) hρ hμ
    cases hr with
    | ok hv => exact ⟨_, _, eval_identL hu h', .ok hv, hμ₁⟩
    | err _ =>
      have hm := mayFail_sound (H := H) hσ hB h
      rw [hf] at hm
      cases hm
  | step hs => exact ih hσ hB (.step hs) hρ hμ

/-- `sim_fwd`, when `e` keeps its shape. -/
theorem sim_fwd_step {H : Hints A} {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) {σ : AEnv A} {e' : Expr} {ρ' : Env} {μ' : Store}
    {N : List String} (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (ho : FwdStep H E σ e e')
    (hρ : EnvRel H E N ρ ρ') (hμ : StoreRel H E μ μ') (hN : ∀ y ∈ freeNames [] e', y ∈ N)
    (hF : E = true → ¬ r.fatal) :
    ∃ r' μ₁', Eval ρ' μ' e' r' μ₁' ∧ OutRel H E r r' ∧ StoreRel H E μ₁ μ₁' := by
  induction h generalizing σ e' ρ' μ' N with
  | int =>
    cases ho with | step ho =>
    cases ho with
    | int => exact ⟨_, _, .int, .ok .int, hμ⟩
  | bool =>
    cases ho with | step ho =>
    cases ho with
    | bool => exact ⟨_, _, .bool, .ok .bool, hμ⟩
  | unit =>
    cases ho with | step ho =>
    cases ho with
    | unit => exact ⟨_, _, .unit, .ok .unit, hμ⟩
  | nil =>
    cases ho with | step ho =>
    cases ho with
    | nil => exact ⟨_, _, .nil, .ok .nil, hμ⟩
  | var hx =>
    cases ho with | step ho =>
    cases ho with
    | var =>
      obtain ⟨w', hw', hv⟩ := hρ.lookup_some (hN _ (by simp [freeNames])) hx
      exact ⟨_, _, .var hw', .ok hv, hμ⟩
  | varErr hx =>
    cases ho with | step ho =>
    cases ho with
    | var => exact ⟨_, _, .varErr (hρ.lookup_none (hN _ (by simp [freeNames])) hx), .err (.same rfl), hμ⟩
  | lam =>
    cases ho with | step ho =>
    cases ho with
    | lam hob => exact ⟨_, _, .lam, .ok (.clos σ N hρ.1 hρ.2 (by fv_sub) hσ hB hob), hμ⟩
  | letrec h2 ih2 =>
    cases ho with | step ho =>
    cases ho with
    | letrec hob ho2 =>
      -- `f` is bound to related closures
      have hf := VR.clos σ N hρ.1 hρ.2 (by fv_sub) hσ hB hob
      obtain ⟨r', μ₁', h2', hr, hμ₁⟩ :=
        lift_fwd h2 ih2 (hσ.cons (letrecVal_mem hσ hB)) hB.cons ho2 (hρ.cons hf) hμ
      exact ⟨_, _, .letrec h2', hr, hμ₁⟩
  | app hf ha hb ihf iha ihb =>
    cases ho with | step ho =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_fwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | ok hvf =>
        -- the optimised function is a closure with an optimised body
        cases hvf with
        | clos σc Nc hc1 hc2 hNc hσc hBc hob =>
          obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_fwd ha iha hσ hB hoa hρ hμ₁
          cases hra with
          | ok hva =>
            obtain ⟨r', μ₃', hb', hr, hμ₃⟩ :=
              lift_fwd hb ihb (describes_bodyEnv hσc hBc) (bound_bodyEnv hBc) hob
                (EnvRel.call ⟨hc1, hc2⟩ hNc hσc hBc hob hva) hμ₂
            exact ⟨_, _, .app hf' ha' hb', hr, hμ₃⟩
  | appNotFn hf hnc ha ihf iha =>
    cases ho with | step ho =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_fwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | ok hvf =>
        obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_fwd ha iha hσ hB hoa hρ hμ₁
        cases hra with
        | ok hva =>
          exact ⟨_, _, .appNotFn hf' (hvf.isClos.trans hnc) ha', .err (.same rfl), hμ₂⟩
  | appErrF hf ihf =>
    cases ho with | step ho =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_fwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | err hk => exact ⟨_, _, .appErrF hf', .err hk, hμ₁⟩
  | appErrA hf ha ihf iha =>
    cases ho with | step ho =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_fwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | ok hvf =>
        obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_fwd ha iha hσ hB hoa hρ hμ₁
        cases hra with
        | err hk => exact ⟨_, _, .appErrA hf' ha', .err hk, hμ₂⟩
  | letin h1 h2 ih1 ih2 =>
    cases ho with
    | letDrop hp hf hx ho2 =>
      -- `e1` doesn't change the store, and `e2'` doesn't use `x`
      obtain ⟨hd, hb⟩ := afterAssert_sound hσ hB h1
      simp at hx
      have hμ1 := pure_store h1 hp
      subst hμ1
      exact lift_fwd h2 ih2 (hd.cons (aeval_sound hσ hB h1)) hb.cons ho2 ((hρ.mono hN).drop hx) hμ
    | step ho =>
    cases ho with
    | letin ho1 ho2 =>
      obtain ⟨r1', μ₁', h1', hr1, hμ₁⟩ := lift_fwd h1 ih1 hσ hB ho1 hρ hμ
      cases hr1 with
      | ok hv1 =>
        -- after `assert c`, `σ` is narrowed by `c` (`afterAssert`)
        obtain ⟨hd, hb⟩ := afterAssert_sound hσ hB h1
        obtain ⟨r', μ₂', h2', hr, hμ₂⟩ :=
          lift_fwd h2 ih2 (hd.cons (aeval_sound hσ hB h1)) hb.cons ho2 (hρ.cons hv1) hμ₁
        exact ⟨_, _, .letin h1' h2', hr, hμ₂⟩
  | letinErr h1 ih1 =>
    cases ho with
    | letDrop hp hf hx ho2 =>
      -- `e1` can't fail, or its error is fatal
      cases hf with
      | inl hf =>
        have hm := mayFail_sound (H := H) hσ hB h1
        rw [hf] at hm
        cases hm
      | inr hf =>
        -- with `E`, the error of `e1` is fatal, but the source run has no fatal error
        obtain ⟨hE, hc⟩ := hf
        have hfatal := onlyFatal_fatal h1 hc
        exact absurd hfatal (hF hE)
    | step ho =>
    cases ho with
    | letin ho1 ho2 =>
      obtain ⟨r1', μ₁', h1', hr1, hμ₁⟩ := lift_fwd h1 ih1 hσ hB ho1 hρ hμ
      cases hr1 with
      | err hk => exact ⟨_, _, .letinErr h1', .err hk, hμ₁⟩
  | ifT hc ht ihc iht =>
    cases ho with
    | iteT hck hot =>
      -- the condition doesn't change the store
      obtain ⟨_, rfl⟩ := constOf_bool hck hσ hB hc
      obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
      rw [hst, Option.getD_some] at hot
      exact lift_fwd ht iht hdt (AEnv.assume_bound hB hst) hot hρ hμ
    | iteF hck hoe => cases (constOf_bool hck hσ hB hc).1
    | step ho =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        -- the `then` branch was optimised knowing that the condition is `true`
        obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc
        rw [hst, Option.getD_some] at hot
        obtain ⟨r', μ₂', ht', hr, hμ₂⟩ := lift_fwd ht iht hdt (AEnv.assume_bound hB hst) hot hρ hμ₁
        exact ⟨_, _, .ifT hc' ht', hr, hμ₂⟩
  | ifF hc he ihc ihe =>
    cases ho with
    | iteT hck hot => cases (constOf_bool hck hσ hB hc).1
    | iteF hck hoe =>
      obtain ⟨_, rfl⟩ := constOf_bool hck hσ hB hc
      obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
      rw [hse, Option.getD_some] at hoe
      exact lift_fwd he ihe hde (AEnv.assume_bound hB hse) hoe hρ hμ
    | step ho =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc
        rw [hse, Option.getD_some] at hoe
        obtain ⟨r', μ₂', he', hr, hμ₂⟩ := lift_fwd he ihe hde (AEnv.assume_bound hB hse) hoe hρ hμ₁
        exact ⟨_, _, .ifF hc' he', hr, hμ₂⟩
  | ifNotBool hc hv ihc =>
    cases ho with
    | iteT hck hot =>
      obtain ⟨heq, _⟩ := constOf_bool hck hσ hB hc
      cases heq
      cases hv
    | iteF hck hoe =>
      obtain ⟨heq, _⟩ := constOf_bool hck hσ hB hc
      cases heq
      cases hv
    | step ho =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc => exact ⟨_, _, .ifNotBool hc' (hvc.isBool.trans hv), .err (.same rfl), hμ₁⟩
  | ifErr hc ihc =>
    cases ho with
    | iteT hck hot => cases (constOf_bool hck hσ hB hc).1
    | iteF hck hoe => cases (constOf_bool hck hσ hB hc).1
    | step ho =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | err hk => exact ⟨_, _, .ifErr hc', .err hk, hμ₁⟩
  | binop ha hb iha ihb =>
    cases ho with | step ho =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | ok hvb => exact ⟨_, _, .binop ha' hb', denote_rel hva hvb, hμ₂⟩
  | binopErrL ha iha =>
    cases ho with | step ho =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .binopErrL ha', .err hk, hμ₁⟩
  | binopErrR ha hb iha ihb =>
    cases ho with | step ho =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | err hk => exact ⟨_, _, .binopErrR ha' hb', .err hk, hμ₂⟩
  | cons ha hb hl iha ihb =>
    cases ho with | step ho =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | ok hvb =>
          exact ⟨_, _, .cons ha' hb' (hvb.isList.trans hl), .ok (.cons hva hvb), hμ₂⟩
  | consNotList ha hb hl iha ihb =>
    cases ho with | step ho =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | ok hvb =>
          exact ⟨_, _, .consNotList ha' hb' (hvb.isList.trans hl), .err (.same rfl), hμ₂⟩
  | consErrL ha iha =>
    cases ho with | step ho =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .consErrL ha', .err hk, hμ₁⟩
  | consErrR ha hb iha ihb =>
    cases ho with | step ho =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | err hk => exact ⟨_, _, .consErrR ha' hb', .err hk, hμ₂⟩
  | matchNil hs hn ihs ihn =>
    cases ho with | step ho =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs
        obtain ⟨r', μ₂', hn', hr, hμ₂⟩ := lift_fwd hn ihn hσ hB hon hρ hμ₁
        exact ⟨_, _, .matchNil hs' hn', hr, hμ₂⟩
  | matchCons hs hc ihs ihc =>
    cases ho with | step ho =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | cons hvh hvt =>
          -- the head is in the heads of the list, and the tail in its tails
          have hv := aeval_sound (H := H) hσ hB hs
          obtain ⟨r', μ₂', hc', hr, hμ₂⟩ :=
            lift_fwd hc ihc
              ((hσ.cons (AVal.mem_ofFlat (AVal.mem_heads hv))).cons (AVal.mem_tails hv))
              hB.cons.cons hoc ((hρ.cons hvh).cons hvt) hμ₁
          exact ⟨_, _, .matchCons hs' hc', hr, hμ₂⟩
  | matchNotList hs hv ihs =>
    cases ho with | step ho =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        exact ⟨_, _, .matchNotList hs' (hvs.isList.trans hv), .err (.same rfl), hμ₁⟩
  | matchErr hs ihs =>
    cases ho with | step ho =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | err hk => exact ⟨_, _, .matchErr hs', .err hk, hμ₁⟩
  | assert hc ihc =>
    cases ho with | step ho =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        exact ⟨_, _, .assert hc', .ok .unit, hμ₁⟩
  | assertF hc ihc =>
    cases ho with | step ho =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        exact ⟨_, _, .assertF hc', .err (.same rfl), hμ₁⟩
  | assertNotBool hc hv ihc =>
    cases ho with | step ho =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        exact ⟨_, _, .assertNotBool hc' (hvc.isBool.trans hv), .err (.same rfl), hμ₁⟩
  | assertErr hc ihc =>
    cases ho with | step ho =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | err hk => exact ⟨_, _, .assertErr hc', .err hk, hμ₁⟩
  | alloc hn hv ihn ihv =>
    cases ho with | step ho =>
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_fwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | ok hvn =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | ok hvv =>
          obtain ⟨hr, hμ₃⟩ := allocV_rel hμ₂ hvn hvv
          exact ⟨_, _, .alloc hn' hv', hr, hμ₃⟩
  | allocErrN hn ihn =>
    cases ho with | step ho =>
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_fwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | err hk => exact ⟨_, _, .allocErrN hn', .err hk, hμ₁⟩
  | allocErrV hn hv ihn ihv =>
    cases ho with | step ho =>
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_fwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | ok hvn =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | err hk => exact ⟨_, _, .allocErrV hn' hv', .err hk, hμ₂⟩
  | get ha hi iha ihi =>
    cases ho with | step ho =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | ok hvi => exact ⟨_, _, .get ha' hi', getV_rel hμ₂ hva hvi, hμ₂⟩
  | getErrA ha iha =>
    cases ho with | step ho =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .getErrA ha', .err hk, hμ₁⟩
  | getErrI ha hi iha ihi =>
    cases ho with | step ho =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | err hk => exact ⟨_, _, .getErrI ha' hi', .err hk, hμ₂⟩
  | set ha hi hv iha ihi ihv =>
    cases ho with | step ho =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | ok hvi =>
          obtain ⟨rv', μ₃', hv', hrv, hμ₃⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₂
          cases hrv with
          | ok hvv =>
            obtain ⟨hr, hμ₄⟩ := setV_rel hμ₃ hva hvi hvv
            exact ⟨_, _, .set ha' hi' hv', hr, hμ₄⟩
  | setErrA ha iha =>
    cases ho with | step ho =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .setErrA ha', .err hk, hμ₁⟩
  | setErrI ha hi iha ihi =>
    cases ho with | step ho =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | err hk => exact ⟨_, _, .setErrI ha' hi', .err hk, hμ₂⟩
  | setErrV ha hi hv iha ihi ihv =>
    cases ho with | step ho =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | ok hvi =>
          obtain ⟨rv', μ₃', hv', hrv, hμ₃⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₂
          cases hrv with
          | err hk => exact ⟨_, _, .setErrV ha' hi' hv', .err hk, hμ₃⟩
  | len ha iha =>
    cases ho with | step ho =>
    cases ho with
    | len hoa =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva => exact ⟨_, _, .len ha', lenV_rel hμ₁ hva, hμ₁⟩
  | lenErr ha iha =>
    cases ho with | step ho =>
    cases ho with
    | len hoa =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .lenErr ha', .err hk, hμ₁⟩
  | ref hv ihv =>
    cases ho with | step ho =>
    cases ho with
    | ref hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv =>
        obtain ⟨hr, hμ₂⟩ := refV_rel hμ₁ hvv
        exact ⟨_, _, .ref hv', hr, hμ₂⟩
  | refErr hv ihv =>
    cases ho with | step ho =>
    cases ho with
    | ref hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .refErr hv', .err hk, hμ₁⟩
  | deref hr ihr =>
    cases ho with | step ho =>
    cases ho with
    | deref hor =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr => exact ⟨_, _, .deref hr', derefV_rel hμ₁ hvr, hμ₁⟩
  | derefErr hr ihr =>
    cases ho with | step ho =>
    cases ho with
    | deref hor =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | err hk => exact ⟨_, _, .derefErr hr', .err hk, hμ₁⟩
  | assign hr hv ihr ihv =>
    cases ho with | step ho =>
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | ok hvv =>
          obtain ⟨hres, hμ₃⟩ := assignV_rel hμ₂ hvr hvv
          exact ⟨_, _, .assign hr' hv', hres, hμ₃⟩
  | assignErrR hr ihr =>
    cases ho with | step ho =>
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | err hk => exact ⟨_, _, .assignErrR hr', .err hk, hμ₁⟩
  | assignErrV hr hv ihr ihv =>
    cases ho with | step ho =>
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | err hk => exact ⟨_, _, .assignErrV hr' hv', .err hk, hμ₂⟩
  | ctor hv ihv =>
    cases ho with | step ho =>
    cases ho with
    | ctor hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .ctor hv', .ok (.ctor hvv), hμ₁⟩
  | ctorErr hv ihv =>
    cases ho with | step ho =>
    cases ho with
    | ctor hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .ctorErr hv', .err hk, hμ₁⟩
  | raise hv hx ihv =>
    cases ho with | step ho =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .raise hv' (hvv.isCtor.trans hx), .err (.exn hvv), hμ₁⟩
  | raiseNotCtor hv hx ihv =>
    cases ho with | step ho =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv =>
        exact ⟨_, _, .raiseNotCtor hv' (hvv.isCtor.trans hx), .err (.same rfl), hμ₁⟩
  | raiseErr hv ihv =>
    cases ho with | step ho =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .raiseErr hv', .err hk, hμ₁⟩
  | tryOk ha iha =>
    cases ho with | step ho =>
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva => exact ⟨_, _, .tryOk ha', .ok hva, hμ₁⟩
  | tryCatch ha hh iha ihh =>
    cases ho with | step ho =>
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk =>
        cases hk with
        | exn hv =>
          obtain ⟨r', μ₂', hh', hr, hμ₂⟩ :=
            lift_fwd hh ihh (hσ.cons (AVal.mem_top _)) hB.cons hoh (hρ.cons hv) hμ₁
          exact ⟨_, _, .tryCatch ha' hh', hr, hμ₂⟩
        | same hx => cases hx
  | tryErr ha hx iha =>
    cases ho with | step ho =>
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .tryErr ha' (hk.isExn.trans hx), .err hk, hμ₁⟩
  | ctorHit hs hh ihs ihh =>
    cases ho with | step ho =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | ctor hv =>
          obtain ⟨r', μ₂', hh', hr, hμ₂⟩ :=
            lift_fwd hh ihh (hσ.cons (AVal.mem_top _)) hB.cons hoh (hρ.cons hv) hμ₁
          exact ⟨_, _, .ctorHit hs' hh', hr, hμ₂⟩
  | ctorMiss hs hne hm ihs ihm =>
    cases ho with | step ho =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | ctor hv =>
          obtain ⟨r', μ₂', hm', hr, hμ₂⟩ := lift_fwd hm ihm hσ hB hom hρ hμ₁
          exact ⟨_, _, .ctorMiss hs' hne hm', hr, hμ₂⟩
  | ctorCaseNotCtor hs hx ihs =>
    cases ho with | step ho =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        exact ⟨_, _, .ctorCaseNotCtor hs' (hvs.isCtor.trans hx), .err (.same rfl), hμ₁⟩
  | ctorCaseErr hs ihs =>
    cases ho with | step ho =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | err hk => exact ⟨_, _, .ctorCaseErr hs', .err hk, hμ₁⟩


/-! ## Backward: what the optimised program does, the source one does too -/

/-- `e'` gives `r'` in `ρ'` and `μ'`. Every `e` related to `e'` by `R`, run in an
    environment related on the free names of `e'`, and in a related store, gives an
    outcome related to `r'`. -/
def BwdSim (H : Hints A) (E : Bool) (R : AEnv A → Expr → Expr → Prop) (ρ' : Env) (μ' : Store)
    (e' : Expr) (r' : Outcome) (μ₁' : Store) : Prop :=
  ∀ {σ : AEnv A} {e : Expr} {ρ : Env} {μ : Store} {N : List String},
    σ.Describes ρ → σ.Bound ρ → R σ e e' → EnvRel H E N ρ ρ' → StoreRel H E μ μ' →
    (hN : ∀ y ∈ freeNames [] e', y ∈ N := by fv_sub) →
    (hS : E = true → ∀ r μ₁, Eval ρ μ e r μ₁ → ¬ r.fatal := by safe_sub) →
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H E r r' ∧ StoreRel H E μ₁ μ₁'

/-- Adds the cases of `fold`, `iteT`, `iteF` and `assertT` to the cases where `e`
    keeps its shape. By recursion on `e`, because the branch kept by `iteT` or `iteF`
    can itself be replaced. -/
theorem lift_bwd {H : Hints A} {ρ' : Env} {μ' μ₁' : Store} {e' : Expr} {r' : Outcome}
    (h : Eval ρ' μ' e' r' μ₁') (ih : BwdSim H E (OptStep H E) ρ' μ' e' r' μ₁')
    {σ : AEnv A} {e : Expr} {ρ : Env} {μ : Store} {N : List String}
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (ho : Optimizes H E σ e e')
    (hρ : EnvRel H E N ρ ρ') (hμ : StoreRel H E μ μ')
    (hN : ∀ y ∈ freeNames [] e', y ∈ N := by fv_sub)
    (hS : E = true → ∀ r μ₁, Eval ρ μ e r μ₁ → ¬ r.fatal := by safe_sub) :
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H E r r' ∧ StoreRel H E μ₁ μ₁' := by
  cases ho with
  | fold hc => exact fold_bwd hc hσ hB h hμ
  | iteT hc hot =>
    -- the condition terminates, gives `true` and doesn't change the store
    obtain ⟨hi, _, _⟩ := constOf_some hc
    obtain ⟨rc, μc, hce⟩ := pure_total _ hi ρ μ
    obtain ⟨rfl, rfl⟩ := constOf_bool hc hσ hB hce
    obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hce
    rw [hst, Option.getD_some] at hot
    obtain ⟨r, μ₁, ht, hr, hμ₁⟩ := lift_bwd h @ih hdt (AEnv.assume_bound hB hst) hot hρ hμ hN
    exact ⟨r, μ₁, .ifT hce ht, hr, hμ₁⟩
  | iteF hc hoe =>
    obtain ⟨hi, _, _⟩ := constOf_some hc
    obtain ⟨rc, μc, hce⟩ := pure_total _ hi ρ μ
    obtain ⟨rfl, rfl⟩ := constOf_bool hc hσ hB hce
    obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hce
    rw [hse, Option.getD_some] at hoe
    obtain ⟨r, μ₁, he, hr, hμ₁⟩ := lift_bwd h @ih hde (AEnv.assume_bound hB hse) hoe hρ hμ hN
    exact ⟨r, μ₁, .ifF hce he, hr, hμ₁⟩
  | assertErase hE hc =>
    -- `c` finishes without changing the store. It gives `true`, because no run of
    -- `assert c` has a fatal error.
    cases h
    obtain ⟨rc, μc, hce⟩ := pure_total _ (isCheck_pure hc) ρ μ
    obtain rfl := pure_store hce (isCheck_pure hc)
    cases rc with
    | err k => exact (hS hE _ _ (.assertErr hce) (isCheck_fatal hce hc)).elim
    | ok v =>
      cases hb : v.isBool
      case false => exact (hS hE _ _ (.assertNotBool hce hb) rfl).elim
      case true =>
        obtain ⟨b, rfl⟩ := bool_of_isBool hb
        cases b
        case false => exact (hS hE _ _ (.assertF hce) rfl).elim
        case true => exact ⟨_, _, .assert hce, .ok .unit, hμ⟩
  | assertT hc =>
    -- `()` gives `()`. `c` terminates, gives `true` and doesn't change the store.
    cases h
    obtain ⟨hi, _, _⟩ := constOf_some hc
    obtain ⟨rc, μc, hce⟩ := pure_total _ hi ρ μ
    obtain ⟨rfl, rfl⟩ := constOf_bool hc hσ hB hce
    exact ⟨_, _, .assert hce, .ok .unit, hμ⟩
  | @identR _ op _ _ _ n hu hb hf hoa =>
    obtain ⟨r, μ₁, ha, hr, hμ₁⟩ := lift_bwd h @ih hσ hB hoa hρ hμ hN
    -- `b` terminates, gives `n` and doesn't change the store
    obtain ⟨hi, _, _⟩ := constOf_some hb
    obtain ⟨rb, μb, hbe⟩ := pure_total _ hi ρ μ₁
    obtain ⟨rfl, rfl⟩ := constOf_int hb hσ hB hbe
    cases r with
    | err k => exact ⟨_, _, .binopErrL ha, hr, hμ₁⟩
    | ok v =>
      have hs := Eval.binop (op := op) ha hbe
      cases hd : op.denote v (.int n) with
      | err k =>
        -- `a op b` can't fail
        rw [hd] at hs
        have hm := mayFail_sound (H := H) hσ hB hs
        rw [hf] at hm
        cases hm
      | ok w =>
        rw [hd] at hs
        obtain rfl := denote_rightUnit_ok hu hd
        exact ⟨_, _, hs, hr, hμ₁⟩
  | @identL _ op _ _ _ n hu ha hf hob =>
    -- `a` terminates, gives `n` and doesn't change the store
    obtain ⟨hi, _, _⟩ := constOf_some ha
    obtain ⟨ra, μa, hae⟩ := pure_total _ hi ρ μ
    obtain ⟨rfl, rfl⟩ := constOf_int ha hσ hB hae
    obtain ⟨r, μ₁, hb, hr, hμ₁⟩ := lift_bwd h @ih hσ hB hob hρ hμ hN
    cases r with
    | err k => exact ⟨_, _, .binopErrR hae hb, hr, hμ₁⟩
    | ok v =>
      have hs := Eval.binop (op := op) hae hb
      cases hd : op.denote (.int n) v with
      | err k =>
        rw [hd] at hs
        have hm := mayFail_sound (H := H) hσ hB hs
        rw [hf] at hm
        cases hm
      | ok w =>
        rw [hd] at hs
        obtain rfl := denote_leftUnit_ok hu hd
        exact ⟨_, _, hs, hr, hμ₁⟩
  | letDrop hp hf hx ho2 =>
    -- `e1` gives a value without changing the store, and `e'` doesn't use `x`
    obtain ⟨r1, μ1, h1⟩ := pure_total _ hp ρ μ
    have hμ1 := pure_store h1 hp
    subst hμ1
    cases r1 with
    | err k =>
      -- `e1` can't fail, or its error is fatal
      cases hf with
      | inl hf =>
        have hm := mayFail_sound (H := H) hσ hB h1
        rw [hf] at hm
        cases hm
      | inr hf =>
        -- with `E`, the error of `e1` is fatal, and it would be the outcome of the `let`
        obtain ⟨hE, hc⟩ := hf
        have hfatal := onlyFatal_fatal h1 hc
        exact absurd hfatal (hS hE _ _ (.letinErr h1))
    | ok v1 =>
      obtain ⟨hd, hb⟩ := afterAssert_sound hσ hB h1
      simp at hx
      obtain ⟨r, μ₁, h2, hr, hμ₁⟩ :=
        lift_bwd h @ih (hd.cons (aeval_sound hσ hB h1)) hb.cons ho2 ((hρ.mono hN).drop hx) hμ
          (fun _ hy => hy)
      exact ⟨r, μ₁, .letin h1 h2, hr, hμ₁⟩
  | step hs => exact ih hσ hB hs hρ hμ
termination_by sizeOf e

/-- `sim_bwd`, when `e` keeps its shape. -/
theorem sim_bwd_step {H : Hints A} {ρ' : Env} {μ' μ₁' : Store} {e' : Expr} {r' : Outcome}
    (h : Eval ρ' μ' e' r' μ₁') {σ : AEnv A} {e : Expr} {ρ : Env} {μ : Store}
    {N : List String} (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (ho : OptStep H E σ e e')
    (hρ : EnvRel H E N ρ ρ') (hμ : StoreRel H E μ μ') (hN : ∀ y ∈ freeNames [] e', y ∈ N)
    (hS : E = true → ∀ r μ₁, Eval ρ μ e r μ₁ → ¬ r.fatal) :
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H E r r' ∧ StoreRel H E μ₁ μ₁' := by
  induction h generalizing σ e ρ μ N with
  | int =>
    cases ho with
    | int => exact ⟨_, _, .int, .ok .int, hμ⟩
  | bool =>
    cases ho with
    | bool => exact ⟨_, _, .bool, .ok .bool, hμ⟩
  | unit =>
    cases ho with
    | unit => exact ⟨_, _, .unit, .ok .unit, hμ⟩
  | nil =>
    cases ho with
    | nil => exact ⟨_, _, .nil, .ok .nil, hμ⟩
  | var hx =>
    cases ho with
    | var =>
      obtain ⟨w', hw', hv⟩ := hρ.lookup_some' (hN _ (by simp [freeNames])) hx
      exact ⟨_, _, .var hw', .ok hv, hμ⟩
  | varErr hx =>
    cases ho with
    | var => exact ⟨_, _, .varErr (hρ.lookup_none' (hN _ (by simp [freeNames])) hx), .err (.same rfl), hμ⟩
  | lam =>
    cases ho with
    | lam hob => exact ⟨_, _, .lam, .ok (.clos σ N hρ.1 hρ.2 (by fv_sub) hσ hB hob), hμ⟩
  | letrec h2 ih2 =>
    cases ho with
    | letrec hob ho2 =>
      -- `f` is bound to related closures
      have hf := VR.clos σ N hρ.1 hρ.2 (by fv_sub) hσ hB hob
      obtain ⟨r', μ₁', h2', hr, hμ₁⟩ :=
        lift_bwd h2 ih2 (hσ.cons (letrecVal_mem hσ hB)) hB.cons ho2 (hρ.cons hf) hμ
      exact ⟨_, _, .letrec h2', hr, hμ₁⟩
  | app hf ha hb ihf iha ihb =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_bwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | ok hvf =>
        -- the optimised function is a closure with an optimised body
        cases hvf with
        | clos σc Nc hc1 hc2 hNc hσc hBc hob =>
          obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_bwd ha iha hσ hB hoa hρ hμ₁
          cases hra with
          | ok hva =>
            obtain ⟨r', μ₃', hb', hr, hμ₃⟩ :=
              lift_bwd hb ihb (describes_bodyEnv hσc hBc) (bound_bodyEnv hBc) hob
                (EnvRel.call ⟨hc1, hc2⟩ hNc hσc hBc hob hva) hμ₂ (hS := fun hE r μ₁ h hf =>
                  hS hE r μ₁ (.app hf' ha' h) hf)
            exact ⟨_, _, .app hf' ha' hb', hr, hμ₃⟩
  | appNotFn hf hnc ha ihf iha =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_bwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | ok hvf =>
        obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_bwd ha iha hσ hB hoa hρ hμ₁
        cases hra with
        | ok hva =>
          exact ⟨_, _, .appNotFn hf' (hvf.isClos.symm.trans hnc) ha', .err (.same rfl), hμ₂⟩
  | appErrF hf ihf =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_bwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | err hk => exact ⟨_, _, .appErrF hf', .err hk, hμ₁⟩
  | appErrA hf ha ihf iha =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_bwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | ok hvf =>
        obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_bwd ha iha hσ hB hoa hρ hμ₁
        cases hra with
        | err hk => exact ⟨_, _, .appErrA hf' ha', .err hk, hμ₂⟩
  | letin h1 h2 ih1 ih2 =>
    cases ho with
    | letin ho1 ho2 =>
      obtain ⟨r1', μ₁', h1', hr1, hμ₁⟩ := lift_bwd h1 ih1 hσ hB ho1 hρ hμ
      cases hr1 with
      | ok hv1 =>
        obtain ⟨hd, hb⟩ := afterAssert_sound hσ hB h1'
        obtain ⟨r', μ₂', h2', hr, hμ₂⟩ :=
          lift_bwd h2 ih2 (hd.cons (aeval_sound hσ hB h1')) hb.cons ho2 (hρ.cons hv1) hμ₁
        exact ⟨_, _, .letin h1' h2', hr, hμ₂⟩
  | letinErr h1 ih1 =>
    cases ho with
    | letin ho1 ho2 =>
      obtain ⟨r1', μ₁', h1', hr1, hμ₁⟩ := lift_bwd h1 ih1 hσ hB ho1 hρ hμ
      cases hr1 with
      | err hk => exact ⟨_, _, .letinErr h1', .err hk, hμ₁⟩
  | ifT hc ht ihc iht =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        -- the `then` branch was optimised knowing that the condition is `true`
        obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hc'
        rw [hst, Option.getD_some] at hot
        obtain ⟨r', μ₂', ht', hr, hμ₂⟩ := lift_bwd ht iht hdt (AEnv.assume_bound hB hst) hot hρ hμ₁
        exact ⟨_, _, .ifT hc' ht', hr, hμ₂⟩
  | ifF hc he ihc ihe =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hc'
        rw [hse, Option.getD_some] at hoe
        obtain ⟨r', μ₂', he', hr, hμ₂⟩ := lift_bwd he ihe hde (AEnv.assume_bound hB hse) hoe hρ hμ₁
        exact ⟨_, _, .ifF hc' he', hr, hμ₂⟩
  | ifNotBool hc hv ihc =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc => exact ⟨_, _, .ifNotBool hc' (hvc.isBool.symm.trans hv), .err (.same rfl), hμ₁⟩
  | ifErr hc ihc =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | err hk => exact ⟨_, _, .ifErr hc', .err hk, hμ₁⟩
  | binop ha hb iha ihb =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_bwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | ok hvb => exact ⟨_, _, .binop ha' hb', denote_rel hva hvb, hμ₂⟩
  | binopErrL ha iha =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .binopErrL ha', .err hk, hμ₁⟩
  | binopErrR ha hb iha ihb =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_bwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | err hk => exact ⟨_, _, .binopErrR ha' hb', .err hk, hμ₂⟩
  | cons ha hb hl iha ihb =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_bwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | ok hvb =>
          exact ⟨_, _, .cons ha' hb' (hvb.isList.symm.trans hl), .ok (.cons hva hvb), hμ₂⟩
  | consNotList ha hb hl iha ihb =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_bwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | ok hvb =>
          exact ⟨_, _, .consNotList ha' hb' (hvb.isList.symm.trans hl), .err (.same rfl), hμ₂⟩
  | consErrL ha iha =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .consErrL ha', .err hk, hμ₁⟩
  | consErrR ha hb iha ihb =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_bwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | err hk => exact ⟨_, _, .consErrR ha' hb', .err hk, hμ₂⟩
  | matchNil hs hn ihs ihn =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs
        obtain ⟨r', μ₂', hn', hr, hμ₂⟩ := lift_bwd hn ihn hσ hB hon hρ hμ₁
        exact ⟨_, _, .matchNil hs' hn', hr, hμ₂⟩
  | matchCons hs hc ihs ihc =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | cons hvh hvt =>
          -- the head is in the heads of the list, and the tail in its tails
          have hv := aeval_sound (H := H) hσ hB hs'
          obtain ⟨r', μ₂', hc', hr, hμ₂⟩ :=
            lift_bwd hc ihc
              ((hσ.cons (AVal.mem_ofFlat (AVal.mem_heads hv))).cons (AVal.mem_tails hv))
              hB.cons.cons hoc ((hρ.cons hvh).cons hvt) hμ₁
          exact ⟨_, _, .matchCons hs' hc', hr, hμ₂⟩
  | matchNotList hs hv ihs =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        exact ⟨_, _, .matchNotList hs' (hvs.isList.symm.trans hv), .err (.same rfl), hμ₁⟩
  | matchErr hs ihs =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | err hk => exact ⟨_, _, .matchErr hs', .err hk, hμ₁⟩
  | assert hc ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        exact ⟨_, _, .assert hc', .ok .unit, hμ₁⟩
  | assertF hc ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        exact ⟨_, _, .assertF hc', .err (.same rfl), hμ₁⟩
  | assertNotBool hc hv ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        exact ⟨_, _, .assertNotBool hc' (hvc.isBool.symm.trans hv), .err (.same rfl), hμ₁⟩
  | assertErr hc ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_bwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | err hk => exact ⟨_, _, .assertErr hc', .err hk, hμ₁⟩
  | alloc hn hv ihn ihv =>
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_bwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | ok hvn =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_bwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | ok hvv =>
          obtain ⟨hr, hμ₃⟩ := allocV_rel hμ₂ hvn hvv
          exact ⟨_, _, .alloc hn' hv', hr, hμ₃⟩
  | allocErrN hn ihn =>
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_bwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | err hk => exact ⟨_, _, .allocErrN hn', .err hk, hμ₁⟩
  | allocErrV hn hv ihn ihv =>
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_bwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | ok hvn =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_bwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | err hk => exact ⟨_, _, .allocErrV hn' hv', .err hk, hμ₂⟩
  | get ha hi iha ihi =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_bwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | ok hvi => exact ⟨_, _, .get ha' hi', getV_rel hμ₂ hva hvi, hμ₂⟩
  | getErrA ha iha =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .getErrA ha', .err hk, hμ₁⟩
  | getErrI ha hi iha ihi =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_bwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | err hk => exact ⟨_, _, .getErrI ha' hi', .err hk, hμ₂⟩
  | set ha hi hv iha ihi ihv =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_bwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | ok hvi =>
          obtain ⟨rv', μ₃', hv', hrv, hμ₃⟩ := lift_bwd hv ihv hσ hB hov hρ hμ₂
            (hS := fun hE r μ₁ h hf => by
              cases r with
              | ok _ => exact hf
              | err k => exact hS hE _ _ (.setErrV ha' hi' h) hf)
          cases hrv with
          | ok hvv =>
            obtain ⟨hr, hμ₄⟩ := setV_rel hμ₃ hva hvi hvv
            exact ⟨_, _, .set ha' hi' hv', hr, hμ₄⟩
  | setErrA ha iha =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .setErrA ha', .err hk, hμ₁⟩
  | setErrI ha hi iha ihi =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_bwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | err hk => exact ⟨_, _, .setErrI ha' hi', .err hk, hμ₂⟩
  | setErrV ha hi hv iha ihi ihv =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_bwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | ok hvi =>
          obtain ⟨rv', μ₃', hv', hrv, hμ₃⟩ := lift_bwd hv ihv hσ hB hov hρ hμ₂
            (hS := fun hE r μ₁ h hf => by
              cases r with
              | ok _ => exact hf
              | err k => exact hS hE _ _ (.setErrV ha' hi' h) hf)
          cases hrv with
          | err hk => exact ⟨_, _, .setErrV ha' hi' hv', .err hk, hμ₃⟩
  | len ha iha =>
    cases ho with
    | len hoa =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva => exact ⟨_, _, .len ha', lenV_rel hμ₁ hva, hμ₁⟩
  | lenErr ha iha =>
    cases ho with
    | len hoa =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .lenErr ha', .err hk, hμ₁⟩
  | ref hv ihv =>
    cases ho with
    | ref hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv =>
        obtain ⟨hr, hμ₂⟩ := refV_rel hμ₁ hvv
        exact ⟨_, _, .ref hv', hr, hμ₂⟩
  | refErr hv ihv =>
    cases ho with
    | ref hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .refErr hv', .err hk, hμ₁⟩
  | deref hr ihr =>
    cases ho with
    | deref hor =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_bwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr => exact ⟨_, _, .deref hr', derefV_rel hμ₁ hvr, hμ₁⟩
  | derefErr hr ihr =>
    cases ho with
    | deref hor =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_bwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | err hk => exact ⟨_, _, .derefErr hr', .err hk, hμ₁⟩
  | assign hr hv ihr ihv =>
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_bwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_bwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | ok hvv =>
          obtain ⟨hres, hμ₃⟩ := assignV_rel hμ₂ hvr hvv
          exact ⟨_, _, .assign hr' hv', hres, hμ₃⟩
  | assignErrR hr ihr =>
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_bwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | err hk => exact ⟨_, _, .assignErrR hr', .err hk, hμ₁⟩
  | assignErrV hr hv ihr ihv =>
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_bwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_bwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | err hk => exact ⟨_, _, .assignErrV hr' hv', .err hk, hμ₂⟩
  | ctor hv ihv =>
    cases ho with
    | ctor hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .ctor hv', .ok (.ctor hvv), hμ₁⟩
  | ctorErr hv ihv =>
    cases ho with
    | ctor hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .ctorErr hv', .err hk, hμ₁⟩
  | raise hv hx ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .raise hv' (hvv.isCtor.symm.trans hx), .err (.exn hvv), hμ₁⟩
  | raiseNotCtor hv hx ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv =>
        exact ⟨_, _, .raiseNotCtor hv' (hvv.isCtor.symm.trans hx), .err (.same rfl), hμ₁⟩
  | raiseErr hv ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .raiseErr hv', .err hk, hμ₁⟩
  | tryOk ha iha =>
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva => exact ⟨_, _, .tryOk ha', .ok hva, hμ₁⟩
  | tryCatch ha hh iha ihh =>
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk =>
        cases hk with
        | exn hv =>
          obtain ⟨r', μ₂', hh', hr, hμ₂⟩ :=
            lift_bwd hh ihh (hσ.cons (AVal.mem_top _)) hB.cons hoh (hρ.cons hv) hμ₁
          exact ⟨_, _, .tryCatch ha' hh', hr, hμ₂⟩
        | same hx => cases hx
  | tryErr ha hx iha =>
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_bwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .tryErr ha' (hk.isExn.symm.trans hx), .err hk, hμ₁⟩
  | ctorHit hs hh ihs ihh =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | ctor hv =>
          obtain ⟨r', μ₂', hh', hr, hμ₂⟩ :=
            lift_bwd hh ihh (hσ.cons (AVal.mem_top _)) hB.cons hoh (hρ.cons hv) hμ₁
          exact ⟨_, _, .ctorHit hs' hh', hr, hμ₂⟩
  | ctorMiss hs hne hm ihs ihm =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | ctor hv =>
          obtain ⟨r', μ₂', hm', hr, hμ₂⟩ := lift_bwd hm ihm hσ hB hom hρ hμ₁
            (hS := fun hE r μ₁ h hf => hS hE r μ₁ (.ctorMiss hs' hne h) hf)
          exact ⟨_, _, .ctorMiss hs' hne hm', hr, hμ₂⟩
  | ctorCaseNotCtor hs hx ihs =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        exact ⟨_, _, .ctorCaseNotCtor hs' (hvs.isCtor.symm.trans hx), .err (.same rfl), hμ₁⟩
  | ctorCaseErr hs ihs =>
    cases ho with
    | ctorCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | err hk => exact ⟨_, _, .ctorCaseErr hs', .err hk, hμ₁⟩

/-- If `e` gives `r`, an optimised version of `e`, run in environments related on its
    free names and in related stores, gives an outcome related to `r`. -/
theorem sim_fwd {H : Hints A} {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) : FwdSim H E (Optimizes H E) ρ μ e r μ₁ := by
  intro σ e' ρ' μ' N hσ hB ho hρ hμ hN hF
  exact lift_fwd h (fun hσ hB ho hρ hμ hN hF => sim_fwd_step h hσ hB ho hρ hμ hN hF) hσ hB ho hρ hμ

/-- If an optimised version of `e` gives `r'`, `e`, run in environments related on the
    free names of the optimised version and in related stores, gives an outcome related
    to `r'`. -/
theorem sim_bwd {H : Hints A} {ρ' : Env} {μ' μ₁' : Store} {e' : Expr} {r' : Outcome}
    (h : Eval ρ' μ' e' r' μ₁') : BwdSim H E (Optimizes H E) ρ' μ' e' r' μ₁' := by
  intro σ e ρ μ N hσ hB ho hρ hμ hN hS
  exact lift_bwd h (fun hσ hB ho hρ hμ hN hS => sim_bwd_step h hσ hB ho hρ hμ hN hS) hσ hB ho hρ hμ

/-! ## The theorem -/

/-- **The optimiser preserves the meaning of programs**, whatever the hints `H`. The
    hints only decide what `opt` rewrites: `opt` checks each fact that it uses. -/
theorem opt_correct (H : Hints A) (e : Expr) :
    Equiv H false e (opt H false ([] : AEnv A) e) := by
  have ho := optimizes_opt (E := false) H e []
  constructor
  · intro r μ h
    -- the environments are empty, so they are related on any names
    exact sim_fwd h AEnv.Describes.nil AEnv.Bound.nil ho EnvRel.nil StoreRel.nil (fun _ hy => hy) (fun hE => by cases hE)
  · intro r' μ' h'
    exact sim_bwd h' AEnv.Describes.nil AEnv.Bound.nil ho EnvRel.nil StoreRel.nil (fun _ hy => hy) (fun hE => by cases hE)

/-- **Erasing the checks preserves the meaning of programs that never fail.** With `E`,
    `opt` also replaces each `assert c`, where `c` is a check, by `()`. If no run of `e`
    ends in a fatal error, `c` gives `true` whenever it is run, so the assertion does
    nothing. -/
theorem opt_erase_correct (H : Hints A) (e : Expr)
    (hsafe : ∀ r μ, Eval [] [] e r μ → ¬ r.fatal) :
    Equiv H true e (opt H true ([] : AEnv A) e) := by
  have ho := optimizes_opt (E := true) H e []
  constructor
  · intro r μ h
    exact sim_fwd h AEnv.Describes.nil AEnv.Bound.nil ho EnvRel.nil StoreRel.nil (fun _ hy => hy)
      (fun _ => hsafe r μ h)
  · intro r' μ' h'
    exact sim_bwd h' AEnv.Describes.nil AEnv.Bound.nil ho EnvRel.nil StoreRel.nil (fun _ hy => hy)
      (fun _ => hsafe)

/-- `opt_erase_correct`, when the analysis proves that `e` never fails. -/
theorem opt_erase_correct_of_mayFail (H : Hints A) (e : Expr)
    (hsafe : mayFail H ([] : AEnv A) e = false) :
    Equiv H true e (opt H true ([] : AEnv A) e) := by
  apply opt_erase_correct
  intro r μ h hf
  cases r with
  | ok _ => exact hf
  | err k =>
    have hm := mayFail_sound (H := H) AEnv.Describes.nil AEnv.Bound.nil h
    rw [hsafe] at hm
    cases hm

/-- **The optimiser preserves the meaning of programs**, with the inferred hints. -/
theorem optimize_correct (e : Expr) :
    Equiv (inferHints ([] : AEnv A) e) false e (optimize ([] : AEnv A) e) :=
  opt_correct _ e

end Diva.Opt
