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

variable {A : Type} [NumDomain A]

/-! ## The optimiser as a relation -/

mutual
/-- `e'` is an optimised version of `e`, in the abstract environment `σ`. `opt H σ e`
    is one (`optimizes_opt`). Stating it as a relation lets the proofs use `cases` on
    the optimised expression. Either `e` is replaced by its value `c` (`fold`), or
    `if` is replaced by the branch that its condition selects (`iteT`, `iteF`), or
    `e` keeps its shape and its sub-expressions are optimised (`step`). -/
inductive Optimizes (H : Hints A) : AEnv A → Expr → Expr → Prop where
  | fold {σ e c} : constOf H σ e = some c → Optimizes H σ e c
  | iteT {σ c t t' e} : constOf H σ c = some (.bool true) →
      Optimizes H ((σ.assume c true).getD σ) t t' → Optimizes H σ (.ite c t e) t'
  | iteF {σ c t e e'} : constOf H σ c = some (.bool false) →
      Optimizes H ((σ.assume c false).getD σ) e e' → Optimizes H σ (.ite c t e) e'
  | step {σ e e'} : OptStep H σ e e' → Optimizes H σ e e'

/-- `e'` has the shape of `e`, and each sub-expression of `e'` is an optimised version
    of the matching sub-expression of `e`. -/
inductive OptStep (H : Hints A) : AEnv A → Expr → Expr → Prop where
  | int {σ n} : OptStep H σ (.int n) (.int n)
  | bool {σ b} : OptStep H σ (.bool b) (.bool b)
  | unit {σ} : OptStep H σ .unit .unit
  | nil {σ} : OptStep H σ .nil .nil
  | var {σ x} : OptStep H σ (.var x) (.var x)
  | lam {σ x b b'} :
      Optimizes H (bodyEnv H σ none x b) b b' → OptStep H σ (.lam x b) (.lam x b')
  | letrec {σ f x b b' e e'} :
      Optimizes H (bodyEnv H σ (some f) x b) b b' →
      Optimizes H ((f, letrecVal H σ f x b) :: σ) e e' →
      OptStep H σ (.letrec f x b e) (.letrec f x b' e')
  | app {σ f f' a a'} :
      Optimizes H σ f f' → Optimizes H σ a a' → OptStep H σ (.app f a) (.app f' a')
  | letin {σ x e1 e1' e2 e2'} :
      Optimizes H σ e1 e1' → Optimizes H ((x, aeval H σ e1) :: σ) e2 e2' →
      OptStep H σ (.letin x e1 e2) (.letin x e1' e2')
  | binop {σ op a a' b b'} :
      Optimizes H σ a a' → Optimizes H σ b b' →
      OptStep H σ (.binop op a b) (.binop op a' b')
  | cons {σ a a' b b'} :
      Optimizes H σ a a' → Optimizes H σ b b' → OptStep H σ (.cons a b) (.cons a' b')
  | ite {σ c c' t t' e e'} :
      Optimizes H σ c c' → Optimizes H ((σ.assume c true).getD σ) t t' →
      Optimizes H ((σ.assume c false).getD σ) e e' →
      OptStep H σ (.ite c t e) (.ite c' t' e')
  | matchList {σ s s' n n' x xs c c'} :
      Optimizes H σ s s' → Optimizes H σ n n' →
      Optimizes H ((xs, (aeval H σ s).tails) :: (x, AVal.ofFlat (aeval H σ s).heads) :: σ)
        c c' →
      OptStep H σ (.matchList s n x xs c) (.matchList s' n' x xs c')
  | assert {σ c c'} : Optimizes H σ c c' → OptStep H σ (.assert c) (.assert c')
  | alloc {σ site n n' v v'} :
      Optimizes H σ n n' → Optimizes H σ v v' →
      OptStep H σ (.alloc site n v) (.alloc site n' v')
  | get {σ a a' i i'} :
      Optimizes H σ a a' → Optimizes H σ i i' → OptStep H σ (.get a i) (.get a' i')
  | set {σ a a' i i' v v'} :
      Optimizes H σ a a' → Optimizes H σ i i' → Optimizes H σ v v' →
      OptStep H σ (.set a i v) (.set a' i' v')
  | len {σ a a'} : Optimizes H σ a a' → OptStep H σ (.len a) (.len a')
  | ref {σ site v v'} : Optimizes H σ v v' → OptStep H σ (.ref site v) (.ref site v')
  | deref {σ r r'} : Optimizes H σ r r' → OptStep H σ (.deref r) (.deref r')
  | assign {σ r r' v v'} :
      Optimizes H σ r r' → Optimizes H σ v v' → OptStep H σ (.assign r v) (.assign r' v')
  | exn {σ t v v'} : Optimizes H σ v v' → OptStep H σ (.exn t v) (.exn t v')
  | raise {σ v v'} : Optimizes H σ v v' → OptStep H σ (.raise v) (.raise v')
  | tryw {σ a a' k h h'} :
      Optimizes H σ a a' → Optimizes H ((k, AVal.top) :: σ) h h' →
      OptStep H σ (.tryw a k h) (.tryw a' k h')
  | exnCase {σ s s' t x h h' m m'} :
      Optimizes H σ s s' → Optimizes H ((x, AVal.top) :: σ) h h' → Optimizes H σ m m' →
      OptStep H σ (.exnCase s t x h m) (.exnCase s' t x h' m')
end

/-- `opt H σ e` is an optimised version of `e`, when `constOf` gives `none` too. -/
theorem optimizes_of_none {H : Hints A} {σ : AEnv A} {e : Expr}
    (h : constOf H σ e = none → OptStep H σ e (opt H σ e)) :
    Optimizes H σ e (opt H σ e) := by
  cases hc : constOf H σ e
  case none => exact .step (h hc)
  case some c =>
    rw [opt.eq_def, hc]
    exact .fold hc

/-- `opt H σ e` is an optimised version of `e`. -/
theorem optimizes_opt (H : Hints A) (e : Expr) : ∀ σ, Optimizes H σ e (opt H σ e) := by
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
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .letin (ih1 _) (ih2 _)
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
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .binop (iha _) (ihb _)
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
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .assert (ih _)
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
  | exn t v ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .exn (ih _)
  | raise v ih =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .raise (ih _)
  | tryw a k h iha ihh =>
    intro σ
    exact optimizes_of_none fun hc => by rw [opt.eq_def, hc]; exact .tryw (iha _) (ihh _)
  | exnCase s t x h m ihs ihh ihm =>
    intro σ
    exact optimizes_of_none fun hc => by
      rw [opt.eq_def, hc]
      exact .exnCase (ihs _) (ihh _) (ihm _)

/-! ## Related values, outcomes and stores

"Related" means equal, except for closures. A closure of the optimised program holds
the optimised body, because `opt` also optimises inside `fun`. Two closures are
related when the second body is an optimised version of the first, and their
environments are related. Environments, errors, outcomes and stores are related
when the values they hold are related.
-/

/-- A source value and an optimised value that agree. -/
inductive VR (H : Hints A) : Value → Value → Prop where
  | int {n : Int} : VR H (.int n) (.int n)
  | bool {b : Bool} : VR H (.bool b) (.bool b)
  | unit : VR H .unit .unit
  | nil : VR H .nil .nil
  | cons {a a' b b' : Value} : VR H a a' → VR H b b' → VR H (.cons a b) (.cons a' b')
  | arr {l : Nat} : VR H (.arr l) (.arr l)
  | ref {l : Nat} : VR H (.ref l) (.ref l)
  | exn {t : String} {a a' : Value} : VR H a a' → VR H (.exn t a) (.exn t a')
  -- the optimised closure has an optimised body, and a related environment. `σ`
  -- describes the source closure's environment.
  | clos {s : Option String} {x : String} {b b' : Expr} {ρ ρ' : Env} (σ : AEnv A) :
      (∀ y w w', ρ.lookup y = some w → ρ'.lookup y = some w' → VR H w w') →
      (∀ y, (ρ.lookup y).isSome = (ρ'.lookup y).isSome) →
      σ.Describes ρ → σ.Bound ρ →
      Optimizes H (bodyEnv H σ s x b) b b' →
      VR H (.clos s x b ρ) (.clos s x b' ρ')

/-- Related environments: the same names, bound to related values. -/
def EnvRel (H : Hints A) (ρ ρ' : Env) : Prop :=
  (∀ y w w', ρ.lookup y = some w → ρ'.lookup y = some w' → VR H w w') ∧
  (∀ y, (ρ.lookup y).isSome = (ρ'.lookup y).isSome)

/-- Related errors: related raised exceptions, or the same runtime error. -/
inductive ErrRel (H : Hints A) : Err → Err → Prop where
  | exn {v v' : Value} : VR H v v' → ErrRel H (.exn v) (.exn v')
  | same {k : Err} : k.isExn = false → ErrRel H k k

/-- Related outcomes: related values, or related errors. -/
inductive OutRel (H : Hints A) : Outcome → Outcome → Prop where
  | ok {v v' : Value} : VR H v v' → OutRel H (.ok v) (.ok v')
  | err {k k' : Err} : ErrRel H k k' → OutRel H (.err k) (.err k')

/-- Related contents of one address: the same length, and related values. -/
def CellRel (H : Hints A) (c c' : List Value) : Prop :=
  c.length = c'.length ∧ ∀ (i : Nat) v v', c[i]? = some v → c'[i]? = some v' → VR H v v'

/-- Related stores: the same addresses, with related contents. -/
def StoreRel (H : Hints A) (μ μ' : Store) : Prop :=
  μ.length = μ'.length ∧
  ∀ (l : Nat) (c c' : List Value), μ[l]? = some c → μ'[l]? = some c' → CellRel H c c'

/-- Two programs without free variables are equivalent: each gives an outcome iff
    the other does, and the outcomes and final stores are related. -/
def Equiv (H : Hints A) (e e' : Expr) : Prop :=
  (∀ r μ, Eval [] [] e r μ → ∃ r' μ', Eval [] [] e' r' μ' ∧ OutRel H r r' ∧ StoreRel H μ μ') ∧
  (∀ r' μ', Eval [] [] e' r' μ' → ∃ r μ, Eval [] [] e r μ ∧ OutRel H r r' ∧ StoreRel H μ μ')

/-! ## Related values -/

namespace VR

variable {H : Hints A} {v v' : Value}

/-- On integers, related means equal. -/
theorem int_eq {n : Int} (h : VR H (.int n) v) : v = .int n := by
  cases h
  rfl

theorem isClos (h : VR H v v') : v'.isClos = v.isClos := by
  cases h <;> rfl

theorem isBool (h : VR H v v') : v'.isBool = v.isBool := by
  cases h <;> rfl

theorem isList (h : VR H v v') : v'.isList = v.isList := by
  cases h <;> rfl

theorem isExn (h : VR H v v') : v'.isExn = v.isExn := by
  cases h <;> rfl

end VR

theorem ErrRel.isExn {H : Hints A} {k k' : Err} (h : ErrRel H k k') : k'.isExn = k.isExn := by
  cases h
  case exn => rfl
  case same => rfl

/-! ## Related environments -/

namespace EnvRel

variable {H : Hints A} {ρ ρ' : Env}

theorem nil : EnvRel H [] [] := by
  constructor
  · intro y w w' hw
    simp [List.lookup] at hw
  · intro y
    rfl

theorem cons {x : String} {v v' : Value} (hρ : EnvRel H ρ ρ') (hv : VR H v v') :
    EnvRel H ((x, v) :: ρ) ((x, v') :: ρ') := by
  constructor
  · intro y w w' hw hw'
    by_cases hxy : y = x
    · subst hxy
      simp [List.lookup] at hw hw'
      subst hw
      subst hw'
      exact hv
    · have hne : (y == x) = false := by simpa using hxy
      simp only [List.lookup, hne] at hw hw'
      exact hρ.1 y w w' hw hw'
  · intro y
    by_cases hxy : y = x
    · subst hxy
      simp [List.lookup]
    · have hne : (y == x) = false := by simpa using hxy
      simp only [List.lookup, hne]
      exact hρ.2 y

/-- A name bound in the source environment is bound in the optimised one, to a
    related value. -/
theorem lookup_some {y : String} {w : Value} (hρ : EnvRel H ρ ρ') (hw : ρ.lookup y = some w) :
    ∃ w', ρ'.lookup y = some w' ∧ VR H w w' := by
  cases hw' : ρ'.lookup y
  case none =>
    have hs := hρ.2 y
    simp [hw, hw'] at hs
  case some w' => exact ⟨w', rfl, hρ.1 y w w' hw hw'⟩

/-- A name bound in the optimised environment is bound in the source one, to a
    related value. -/
theorem lookup_some' {y : String} {w' : Value} (hρ : EnvRel H ρ ρ')
    (hw' : ρ'.lookup y = some w') : ∃ w, ρ.lookup y = some w ∧ VR H w w' := by
  cases hw : ρ.lookup y
  case none =>
    have hs := hρ.2 y
    simp [hw, hw'] at hs
  case some w => exact ⟨w, rfl, hρ.1 y w w' hw hw'⟩

theorem lookup_none {y : String} (hρ : EnvRel H ρ ρ') (h : ρ.lookup y = none) :
    ρ'.lookup y = none := by
  have hs := hρ.2 y
  rw [h] at hs
  cases hw' : ρ'.lookup y
  case none => rfl
  case some w' => simp [hw'] at hs

theorem lookup_none' {y : String} (hρ : EnvRel H ρ ρ') (h : ρ'.lookup y = none) :
    ρ.lookup y = none := by
  have hs := hρ.2 y
  rw [h] at hs
  cases hw : ρ.lookup y
  case none => rfl
  case some w => simp [hw] at hs

/-- Related closures called on related arguments run their bodies in related
    environments. -/
theorem call {s : Option String} {x : String} {b b' : Expr} {σ : AEnv A} {va va' : Value}
    (hρ : EnvRel H ρ ρ') (hσ : σ.Describes ρ) (hB : σ.Bound ρ)
    (hb : Optimizes H (bodyEnv H σ s x b) b b') (hv : VR H va va') :
    EnvRel H (callEnv s x b ρ va) (callEnv s x b' ρ' va') := by
  cases s
  case none => exact hρ.cons hv
  case some f => exact (hρ.cons (.clos σ hρ.1 hρ.2 hσ hB hb)).cons hv

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

theorem get! {n : Nat} (hc : CellRel H c c') (hn : n < c.length) : VR H c[n]! c'[n]! := by
  have hn' : n < c'.length := hc.1 ▸ hn
  rw [getElem!_pos c n hn, getElem!_pos c' n hn']
  exact hc.2 n _ _ (List.getElem?_eq_getElem hn) (List.getElem?_eq_getElem hn')

theorem replicate {v v' : Value} (n : Nat) (hv : VR H v v') :
    CellRel H (List.replicate n v) (List.replicate n v') := by
  constructor
  · simp
  · intro i w w' hw hw'
    simp [List.getElem?_replicate] at hw hw'
    rw [← hw.2, ← hw'.2]
    exact hv

theorem single {v v' : Value} (hv : VR H v v') : CellRel H [v] [v'] :=
  CellRel.replicate 1 hv

theorem set {v v' : Value} (hc : CellRel H c c') (i : Nat) (hv : VR H v v') :
    CellRel H (c.set i v) (c'.set i v') := by
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

theorem nil : StoreRel H [] [] := by
  constructor
  · rfl
  · intro l c c' hc
    simp at hc

/-- An address holds contents in both stores, or in neither. The contents are
    related. -/
theorem get (hμ : StoreRel H μ μ') (l : Nat) :
    (μ[l]? = none ∧ μ'[l]? = none) ∨
    ∃ c c', μ[l]? = some c ∧ μ'[l]? = some c' ∧ CellRel H c c' := by
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

theorem append {c c' : List Value} (hμ : StoreRel H μ μ') (hc : CellRel H c c') :
    StoreRel H (μ ++ [c]) (μ' ++ [c']) := by
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

theorem set {c c' : List Value} (hμ : StoreRel H μ μ') (l : Nat) (hc : CellRel H c c') :
    StoreRel H (μ.set l c) (μ'.set l c') := by
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

theorem allocV_rel {vn vn' vv vv' : Value} (hμ : StoreRel H μ μ') (hn : VR H vn vn')
    (hv : VR H vv vv') :
    OutRel H (allocV μ vn vv).1 (allocV μ' vn' vv').1 ∧
    StoreRel H (allocV μ vn vv).2 (allocV μ' vn' vv').2 := by
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

theorem getV_rel {va va' vi vi' : Value} (hμ : StoreRel H μ μ') (ha : VR H va va')
    (hi : VR H vi vi') : OutRel H (getV μ va vi) (getV μ' va' vi') := by
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

theorem setV_rel {va va' vi vi' vv vv' : Value} (hμ : StoreRel H μ μ') (ha : VR H va va')
    (hi : VR H vi vi') (hv : VR H vv vv') :
    OutRel H (setV μ va vi vv).1 (setV μ' va' vi' vv').1 ∧
    StoreRel H (setV μ va vi vv).2 (setV μ' va' vi' vv').2 := by
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

theorem lenV_rel {va va' : Value} (hμ : StoreRel H μ μ') (ha : VR H va va') :
    OutRel H (lenV μ va) (lenV μ' va') := by
  cases ha
  case arr l =>
    rcases hμ.get l with ⟨h1, h2⟩ | ⟨c, c', h1, h2, hc⟩
    · simp only [lenV, h1, h2]
      exact .err (.same rfl)
    · simp only [lenV, h1, h2, hc.1]
      exact .ok .int
  all_goals exact .err (.same rfl)

theorem refV_rel {v v' : Value} (hμ : StoreRel H μ μ') (hv : VR H v v') :
    OutRel H (refV μ v).1 (refV μ' v').1 ∧ StoreRel H (refV μ v).2 (refV μ' v').2 := by
  simp only [refV]
  rw [hμ.1]
  exact ⟨.ok .ref, hμ.append (CellRel.single hv)⟩

theorem derefV_rel {vr vr' : Value} (hμ : StoreRel H μ μ') (hr : VR H vr vr') :
    OutRel H (derefV μ vr) (derefV μ' vr') := by
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

theorem assignV_rel {vr vr' v v' : Value} (hμ : StoreRel H μ μ') (hr : VR H vr vr')
    (hv : VR H v v') :
    OutRel H (assignV μ vr v).1 (assignV μ' vr' v').1 ∧
    StoreRel H (assignV μ vr v).2 (assignV μ' vr' v').2 := by
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
    OutRel H (op.denote va vb) (op.denote va vb) := by
  cases h : op.denote va vb with
  | ok v =>
    rcases denote_ok_plain h with ⟨n, rfl⟩ | ⟨b, rfl⟩
    · exact .ok .int
    · exact .ok .bool
  | err k => exact .err (.same (denote_err_plain h))

/-- A binary operator looks only at integers, booleans and `()`, on which related
    values are equal. -/
theorem denote_eq {op : BinOp} {va va' vb vb' : Value} (ha : VR H va va') (hb : VR H vb vb') :
    op.denote va' vb' = op.denote va vb := by
  cases ha <;> cases hb <;> cases op <;> rfl

theorem denote_rel {op : BinOp} {va va' vb vb' : Value} (ha : VR H va va') (hb : VR H vb vb') :
    OutRel H (op.denote va vb) (op.denote va' vb') := by
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

theorem exn_of_isExn {v : Value} (h : v.isExn = true) : ∃ t w, v = .exn t w := by
  cases v
  case exn t w => exact ⟨t, w, rfl⟩
  all_goals simp [Value.isExn] at h

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
  | exnCaseNotExn _ _ ihc | exnCaseErr _ ihc =>
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
  | matchNil _ _ ihs ihn | exnHit _ _ ihs ihn =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [ihn hi.1.2, ihs hi.1.1]
  | matchCons _ _ ihs ihc | exnMiss _ _ _ ihs ihc =>
    intro hi
    simp only [Expr.pure, Bool.and_eq_true] at hi
    rw [ihc hi.2, ihs hi.1.1]
  | assert _ ih | assertF _ ih | assertNotBool _ _ ih | assertErr _ ih | len _ ih
  | lenErr _ ih | deref _ ih | derefErr _ ih | exn _ ih | exnErr _ ih | raise _ _ ih
  | raiseNotExn _ _ ih | raiseErr _ ih =>
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
  | exn t v ih =>
    intro hi ρ μ
    obtain ⟨rv, μ₁, hv⟩ := ih hi ρ μ
    cases rv with
    | err k => exact ⟨_, _, .exnErr hv⟩
    | ok w => exact ⟨_, _, .exn hv⟩
  | raise v ih =>
    intro hi ρ μ
    obtain ⟨rv, μ₁, hv⟩ := ih hi ρ μ
    cases rv with
    | err k => exact ⟨_, _, .raiseErr hv⟩
    | ok w =>
      cases hx : w.isExn
      case true => exact ⟨_, _, .raise hv hx⟩
      case false => exact ⟨_, _, .raiseNotExn hv hx⟩
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
  | exnCase s t x h m ihs ihh ihm =>
    intro hi ρ μ
    simp only [Expr.pure, Bool.and_eq_true] at hi
    obtain ⟨rs, μ₁, hs⟩ := ihs hi.1.1 ρ μ
    cases rs with
    | err k => exact ⟨_, _, .exnCaseErr hs⟩
    | ok v =>
      cases hx : v.isExn
      case false => exact ⟨_, _, .exnCaseNotExn hs hx⟩
      case true =>
        obtain ⟨t', w, rfl⟩ := exn_of_isExn hx
        by_cases ht : t' = t
        · subst ht
          obtain ⟨r, μ₂, hh⟩ := ihh hi.1.2 ((x, w) :: ρ) μ₁
          exact ⟨_, _, .exnHit hs hh⟩
        · obtain ⟨r, μ₂, hm⟩ := ihm hi.2 ρ μ₁
          exact ⟨_, _, .exnMiss hs ht hm⟩

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
    (h : Eval ρ μ e r μ₁) (hμ : StoreRel H μ μ') :
    ∃ r' μ₁', Eval ρ' μ' c r' μ₁' ∧ OutRel H r r' ∧ StoreRel H μ₁ μ₁' := by
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
    (h' : Eval ρ' μ' c r' μ₁') (hμ : StoreRel H μ μ') :
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H r r' ∧ StoreRel H μ₁ μ₁' := by
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


/-! ## Forward: what the source program does, the optimised one does too -/

/-- `e` gives `r` in `ρ` and `μ`. Every `e'` related to `e` by `R`, run in related
    environments and stores, gives an outcome related to `r`. -/
def FwdSim (H : Hints A) (R : AEnv A → Expr → Expr → Prop) (ρ : Env) (μ : Store)
    (e : Expr) (r : Outcome) (μ₁ : Store) : Prop :=
  ∀ {σ : AEnv A} {e' : Expr} {ρ' : Env} {μ' : Store}, σ.Describes ρ → σ.Bound ρ →
    R σ e e' → EnvRel H ρ ρ' → StoreRel H μ μ' →
    ∃ r' μ₁', Eval ρ' μ' e' r' μ₁' ∧ OutRel H r r' ∧ StoreRel H μ₁ μ₁'

/-- Adds the cases where `e` is replaced by its value (`fold_fwd`) or by a branch
    (`iteT`, `iteF`) to the cases where `e` keeps its shape. -/
theorem lift_fwd {H : Hints A} {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) (ih : FwdSim H (OptStep H) ρ μ e r μ₁) :
    FwdSim H (Optimizes H) ρ μ e r μ₁ := by
  intro σ e' ρ' μ' hσ hB ho hρ hμ
  cases ho with
  | fold hc => exact fold_fwd hc hσ hB h hμ
  | iteT hc hot =>
    -- `if true then t' else ...` is related to `e` by `OptStep`, and gives what `t'` gives
    obtain ⟨r', μ₁', h', hr, hμ₁⟩ :=
      ih hσ hB (.ite (.fold hc) hot (optimizes_opt H _ _)) hρ hμ
    exact ⟨r', μ₁', eval_ite_true h', hr, hμ₁⟩
  | iteF hc hoe =>
    obtain ⟨r', μ₁', h', hr, hμ₁⟩ :=
      ih hσ hB (.ite (.fold hc) (optimizes_opt H _ _) hoe) hρ hμ
    exact ⟨r', μ₁', eval_ite_false h', hr, hμ₁⟩
  | step hs => exact ih hσ hB hs hρ hμ

/-- `sim_fwd`, when `e` keeps its shape. -/
theorem sim_fwd_step {H : Hints A} {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) {σ : AEnv A} {e' : Expr} {ρ' : Env} {μ' : Store}
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (ho : OptStep H σ e e')
    (hρ : EnvRel H ρ ρ') (hμ : StoreRel H μ μ') :
    ∃ r' μ₁', Eval ρ' μ' e' r' μ₁' ∧ OutRel H r r' ∧ StoreRel H μ₁ μ₁' := by
  induction h generalizing σ e' ρ' μ' with
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
      obtain ⟨w', hw', hv⟩ := hρ.lookup_some hx
      exact ⟨_, _, .var hw', .ok hv, hμ⟩
  | varErr hx =>
    cases ho with
    | var => exact ⟨_, _, .varErr (hρ.lookup_none hx), .err (.same rfl), hμ⟩
  | lam =>
    cases ho with
    | lam hob => exact ⟨_, _, .lam, .ok (.clos σ hρ.1 hρ.2 hσ hB hob), hμ⟩
  | letrec h2 ih2 =>
    cases ho with
    | letrec hob ho2 =>
      -- `f` is bound to related closures
      have hf := VR.clos σ hρ.1 hρ.2 hσ hB hob
      obtain ⟨r', μ₁', h2', hr, hμ₁⟩ :=
        lift_fwd h2 ih2 (hσ.cons (letrecVal_mem hσ hB)) hB.cons ho2 (hρ.cons hf) hμ
      exact ⟨_, _, .letrec h2', hr, hμ₁⟩
  | app hf ha hb ihf iha ihb =>
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_fwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | ok hvf =>
        -- the optimised function is a closure with an optimised body
        cases hvf with
        | clos σc hc1 hc2 hσc hBc hob =>
          obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_fwd ha iha hσ hB hoa hρ hμ₁
          cases hra with
          | ok hva =>
            obtain ⟨r', μ₃', hb', hr, hμ₃⟩ :=
              lift_fwd hb ihb (describes_bodyEnv hσc hBc) (bound_bodyEnv hBc) hob
                (EnvRel.call ⟨hc1, hc2⟩ hσc hBc hob hva) hμ₂
            exact ⟨_, _, .app hf' ha' hb', hr, hμ₃⟩
  | appNotFn hf hnc ha ihf iha =>
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
    cases ho with
    | app hof hoa =>
      obtain ⟨rf', μ₁', hf', hrf, hμ₁⟩ := lift_fwd hf ihf hσ hB hof hρ hμ
      cases hrf with
      | err hk => exact ⟨_, _, .appErrF hf', .err hk, hμ₁⟩
  | appErrA hf ha ihf iha =>
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
    | letin ho1 ho2 =>
      obtain ⟨r1', μ₁', h1', hr1, hμ₁⟩ := lift_fwd h1 ih1 hσ hB ho1 hρ hμ
      cases hr1 with
      | ok hv1 =>
        obtain ⟨r', μ₂', h2', hr, hμ₂⟩ :=
          lift_fwd h2 ih2 (hσ.cons (aeval_sound hσ hB h1)) hB.cons ho2 (hρ.cons hv1) hμ₁
        exact ⟨_, _, .letin h1' h2', hr, hμ₂⟩
  | letinErr h1 ih1 =>
    cases ho with
    | letin ho1 ho2 =>
      obtain ⟨r1', μ₁', h1', hr1, hμ₁⟩ := lift_fwd h1 ih1 hσ hB ho1 hρ hμ
      cases hr1 with
      | err hk => exact ⟨_, _, .letinErr h1', .err hk, hμ₁⟩
  | ifT hc ht ihc iht =>
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
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc => exact ⟨_, _, .ifNotBool hc' (hvc.isBool.trans hv), .err (.same rfl), hμ₁⟩
  | ifErr hc ihc =>
    cases ho with
    | ite hoc hot hoe =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | err hk => exact ⟨_, _, .ifErr hc', .err hk, hμ₁⟩
  | binop ha hb iha ihb =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | ok hvb => exact ⟨_, _, .binop ha' hb', denote_rel hva hvb, hμ₂⟩
  | binopErrL ha iha =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .binopErrL ha', .err hk, hμ₁⟩
  | binopErrR ha hb iha ihb =>
    cases ho with
    | binop hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | err hk => exact ⟨_, _, .binopErrR ha' hb', .err hk, hμ₂⟩
  | cons ha hb hl iha ihb =>
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
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .consErrL ha', .err hk, hμ₁⟩
  | consErrR ha hb iha ihb =>
    cases ho with
    | cons hoa hob =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨rb', μ₂', hb', hrb, hμ₂⟩ := lift_fwd hb ihb hσ hB hob hρ hμ₁
        cases hrb with
        | err hk => exact ⟨_, _, .consErrR ha' hb', .err hk, hμ₂⟩
  | matchNil hs hn ihs ihn =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs
        obtain ⟨r', μ₂', hn', hr, hμ₂⟩ := lift_fwd hn ihn hσ hB hon hρ hμ₁
        exact ⟨_, _, .matchNil hs' hn', hr, hμ₂⟩
  | matchCons hs hc ihs ihc =>
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
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        exact ⟨_, _, .matchNotList hs' (hvs.isList.trans hv), .err (.same rfl), hμ₁⟩
  | matchErr hs ihs =>
    cases ho with
    | matchList hos hon hoc =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | err hk => exact ⟨_, _, .matchErr hs', .err hk, hμ₁⟩
  | assert hc ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        exact ⟨_, _, .assert hc', .ok .unit, hμ₁⟩
  | assertF hc ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        cases hvc
        exact ⟨_, _, .assertF hc', .err (.same rfl), hμ₁⟩
  | assertNotBool hc hv ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | ok hvc =>
        exact ⟨_, _, .assertNotBool hc' (hvc.isBool.trans hv), .err (.same rfl), hμ₁⟩
  | assertErr hc ihc =>
    cases ho with
    | assert hoc =>
      obtain ⟨rc', μ₁', hc', hrc, hμ₁⟩ := lift_fwd hc ihc hσ hB hoc hρ hμ
      cases hrc with
      | err hk => exact ⟨_, _, .assertErr hc', .err hk, hμ₁⟩
  | alloc hn hv ihn ihv =>
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
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_fwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | err hk => exact ⟨_, _, .allocErrN hn', .err hk, hμ₁⟩
  | allocErrV hn hv ihn ihv =>
    cases ho with
    | alloc hon hov =>
      obtain ⟨rn', μ₁', hn', hrn, hμ₁⟩ := lift_fwd hn ihn hσ hB hon hρ hμ
      cases hrn with
      | ok hvn =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | err hk => exact ⟨_, _, .allocErrV hn' hv', .err hk, hμ₂⟩
  | get ha hi iha ihi =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | ok hvi => exact ⟨_, _, .get ha' hi', getV_rel hμ₂ hva hvi, hμ₂⟩
  | getErrA ha iha =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .getErrA ha', .err hk, hμ₁⟩
  | getErrI ha hi iha ihi =>
    cases ho with
    | get hoa hoi =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | err hk => exact ⟨_, _, .getErrI ha' hi', .err hk, hμ₂⟩
  | set ha hi hv iha ihi ihv =>
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
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .setErrA ha', .err hk, hμ₁⟩
  | setErrI ha hi iha ihi =>
    cases ho with
    | set hoa hoi hov =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva =>
        obtain ⟨ri', μ₂', hi', hri, hμ₂⟩ := lift_fwd hi ihi hσ hB hoi hρ hμ₁
        cases hri with
        | err hk => exact ⟨_, _, .setErrI ha' hi', .err hk, hμ₂⟩
  | setErrV ha hi hv iha ihi ihv =>
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
    cases ho with
    | len hoa =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva => exact ⟨_, _, .len ha', lenV_rel hμ₁ hva, hμ₁⟩
  | lenErr ha iha =>
    cases ho with
    | len hoa =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .lenErr ha', .err hk, hμ₁⟩
  | ref hv ihv =>
    cases ho with
    | ref hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv =>
        obtain ⟨hr, hμ₂⟩ := refV_rel hμ₁ hvv
        exact ⟨_, _, .ref hv', hr, hμ₂⟩
  | refErr hv ihv =>
    cases ho with
    | ref hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .refErr hv', .err hk, hμ₁⟩
  | deref hr ihr =>
    cases ho with
    | deref hor =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr => exact ⟨_, _, .deref hr', derefV_rel hμ₁ hvr, hμ₁⟩
  | derefErr hr ihr =>
    cases ho with
    | deref hor =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | err hk => exact ⟨_, _, .derefErr hr', .err hk, hμ₁⟩
  | assign hr hv ihr ihv =>
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
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | err hk => exact ⟨_, _, .assignErrR hr', .err hk, hμ₁⟩
  | assignErrV hr hv ihr ihv =>
    cases ho with
    | assign hor hov =>
      obtain ⟨rr', μ₁', hr', hrr, hμ₁⟩ := lift_fwd hr ihr hσ hB hor hρ hμ
      cases hrr with
      | ok hvr =>
        obtain ⟨rv', μ₂', hv', hrv, hμ₂⟩ := lift_fwd hv ihv hσ hB hov hρ hμ₁
        cases hrv with
        | err hk => exact ⟨_, _, .assignErrV hr' hv', .err hk, hμ₂⟩
  | exn hv ihv =>
    cases ho with
    | exn hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .exn hv', .ok (.exn hvv), hμ₁⟩
  | exnErr hv ihv =>
    cases ho with
    | exn hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .exnErr hv', .err hk, hμ₁⟩
  | raise hv hx ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .raise hv' (hvv.isExn.trans hx), .err (.exn hvv), hμ₁⟩
  | raiseNotExn hv hx ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv =>
        exact ⟨_, _, .raiseNotExn hv' (hvv.isExn.trans hx), .err (.same rfl), hμ₁⟩
  | raiseErr hv ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_fwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .raiseErr hv', .err hk, hμ₁⟩
  | tryOk ha iha =>
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | ok hva => exact ⟨_, _, .tryOk ha', .ok hva, hμ₁⟩
  | tryCatch ha hh iha ihh =>
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
    cases ho with
    | tryw hoa hoh =>
      obtain ⟨ra', μ₁', ha', hra, hμ₁⟩ := lift_fwd ha iha hσ hB hoa hρ hμ
      cases hra with
      | err hk => exact ⟨_, _, .tryErr ha' (hk.isExn.trans hx), .err hk, hμ₁⟩
  | exnHit hs hh ihs ihh =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | exn hv =>
          obtain ⟨r', μ₂', hh', hr, hμ₂⟩ :=
            lift_fwd hh ihh (hσ.cons (AVal.mem_top _)) hB.cons hoh (hρ.cons hv) hμ₁
          exact ⟨_, _, .exnHit hs' hh', hr, hμ₂⟩
  | exnMiss hs hne hm ihs ihm =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | exn hv =>
          obtain ⟨r', μ₂', hm', hr, hμ₂⟩ := lift_fwd hm ihm hσ hB hom hρ hμ₁
          exact ⟨_, _, .exnMiss hs' hne hm', hr, hμ₂⟩
  | exnCaseNotExn hs hx ihs =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        exact ⟨_, _, .exnCaseNotExn hs' (hvs.isExn.trans hx), .err (.same rfl), hμ₁⟩
  | exnCaseErr hs ihs =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_fwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | err hk => exact ⟨_, _, .exnCaseErr hs', .err hk, hμ₁⟩


/-! ## Backward: what the optimised program does, the source one does too -/

/-- `e'` gives `r'` in `ρ'` and `μ'`. Every `e` related to `e'` by `R`, run in related
    environments and stores, gives an outcome related to `r'`. -/
def BwdSim (H : Hints A) (R : AEnv A → Expr → Expr → Prop) (ρ' : Env) (μ' : Store)
    (e' : Expr) (r' : Outcome) (μ₁' : Store) : Prop :=
  ∀ {σ : AEnv A} {e : Expr} {ρ : Env} {μ : Store}, σ.Describes ρ → σ.Bound ρ →
    R σ e e' → EnvRel H ρ ρ' → StoreRel H μ μ' →
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H r r' ∧ StoreRel H μ₁ μ₁'

/-- Adds the cases where `e` is replaced by its value (`fold_bwd`) or by a branch
    (`iteT`, `iteF`) to the cases where `e` keeps its shape. By recursion on `e`,
    because the branch can itself be replaced. -/
theorem lift_bwd {H : Hints A} {ρ' : Env} {μ' μ₁' : Store} {e' : Expr} {r' : Outcome}
    (h : Eval ρ' μ' e' r' μ₁') (ih : BwdSim H (OptStep H) ρ' μ' e' r' μ₁')
    {σ : AEnv A} {e : Expr} {ρ : Env} {μ : Store}
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (ho : Optimizes H σ e e')
    (hρ : EnvRel H ρ ρ') (hμ : StoreRel H μ μ') :
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H r r' ∧ StoreRel H μ₁ μ₁' := by
  cases ho with
  | fold hc => exact fold_bwd hc hσ hB h hμ
  | iteT hc hot =>
    -- the condition terminates, gives `true` and doesn't change the store
    obtain ⟨hi, _, _⟩ := constOf_some hc
    obtain ⟨rc, μc, hce⟩ := pure_total _ hi ρ μ
    obtain ⟨rfl, rfl⟩ := constOf_bool hc hσ hB hce
    obtain ⟨σt, hst, hdt⟩ := σ.assume_sound hσ hce
    rw [hst, Option.getD_some] at hot
    obtain ⟨r, μ₁, ht, hr, hμ₁⟩ := lift_bwd h ih hdt (AEnv.assume_bound hB hst) hot hρ hμ
    exact ⟨r, μ₁, .ifT hce ht, hr, hμ₁⟩
  | iteF hc hoe =>
    obtain ⟨hi, _, _⟩ := constOf_some hc
    obtain ⟨rc, μc, hce⟩ := pure_total _ hi ρ μ
    obtain ⟨rfl, rfl⟩ := constOf_bool hc hσ hB hce
    obtain ⟨σe, hse, hde⟩ := σ.assume_sound hσ hce
    rw [hse, Option.getD_some] at hoe
    obtain ⟨r, μ₁, he, hr, hμ₁⟩ := lift_bwd h ih hde (AEnv.assume_bound hB hse) hoe hρ hμ
    exact ⟨r, μ₁, .ifF hce he, hr, hμ₁⟩
  | step hs => exact ih hσ hB hs hρ hμ
termination_by sizeOf e

/-- `sim_bwd`, when `e` keeps its shape. -/
theorem sim_bwd_step {H : Hints A} {ρ' : Env} {μ' μ₁' : Store} {e' : Expr} {r' : Outcome}
    (h : Eval ρ' μ' e' r' μ₁') {σ : AEnv A} {e : Expr} {ρ : Env} {μ : Store}
    (hσ : σ.Describes ρ) (hB : σ.Bound ρ) (ho : OptStep H σ e e')
    (hρ : EnvRel H ρ ρ') (hμ : StoreRel H μ μ') :
    ∃ r μ₁, Eval ρ μ e r μ₁ ∧ OutRel H r r' ∧ StoreRel H μ₁ μ₁' := by
  induction h generalizing σ e ρ μ with
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
      obtain ⟨w', hw', hv⟩ := hρ.lookup_some' hx
      exact ⟨_, _, .var hw', .ok hv, hμ⟩
  | varErr hx =>
    cases ho with
    | var => exact ⟨_, _, .varErr (hρ.lookup_none' hx), .err (.same rfl), hμ⟩
  | lam =>
    cases ho with
    | lam hob => exact ⟨_, _, .lam, .ok (.clos σ hρ.1 hρ.2 hσ hB hob), hμ⟩
  | letrec h2 ih2 =>
    cases ho with
    | letrec hob ho2 =>
      -- `f` is bound to related closures
      have hf := VR.clos σ hρ.1 hρ.2 hσ hB hob
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
        | clos σc hc1 hc2 hσc hBc hob =>
          obtain ⟨ra', μ₂', ha', hra, hμ₂⟩ := lift_bwd ha iha hσ hB hoa hρ hμ₁
          cases hra with
          | ok hva =>
            obtain ⟨r', μ₃', hb', hr, hμ₃⟩ :=
              lift_bwd hb ihb (describes_bodyEnv hσc hBc) (bound_bodyEnv hBc) hob
                (EnvRel.call ⟨hc1, hc2⟩ hσc hBc hob hva) hμ₂
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
        obtain ⟨r', μ₂', h2', hr, hμ₂⟩ :=
          lift_bwd h2 ih2 (hσ.cons (aeval_sound hσ hB h1')) hB.cons ho2 (hρ.cons hv1) hμ₁
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
  | exn hv ihv =>
    cases ho with
    | exn hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .exn hv', .ok (.exn hvv), hμ₁⟩
  | exnErr hv ihv =>
    cases ho with
    | exn hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | err hk => exact ⟨_, _, .exnErr hv', .err hk, hμ₁⟩
  | raise hv hx ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv => exact ⟨_, _, .raise hv' (hvv.isExn.symm.trans hx), .err (.exn hvv), hμ₁⟩
  | raiseNotExn hv hx ihv =>
    cases ho with
    | raise hov =>
      obtain ⟨rv', μ₁', hv', hrv, hμ₁⟩ := lift_bwd hv ihv hσ hB hov hρ hμ
      cases hrv with
      | ok hvv =>
        exact ⟨_, _, .raiseNotExn hv' (hvv.isExn.symm.trans hx), .err (.same rfl), hμ₁⟩
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
  | exnHit hs hh ihs ihh =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | exn hv =>
          obtain ⟨r', μ₂', hh', hr, hμ₂⟩ :=
            lift_bwd hh ihh (hσ.cons (AVal.mem_top _)) hB.cons hoh (hρ.cons hv) hμ₁
          exact ⟨_, _, .exnHit hs' hh', hr, hμ₂⟩
  | exnMiss hs hne hm ihs ihm =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        cases hvs with
        | exn hv =>
          obtain ⟨r', μ₂', hm', hr, hμ₂⟩ := lift_bwd hm ihm hσ hB hom hρ hμ₁
          exact ⟨_, _, .exnMiss hs' hne hm', hr, hμ₂⟩
  | exnCaseNotExn hs hx ihs =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | ok hvs =>
        exact ⟨_, _, .exnCaseNotExn hs' (hvs.isExn.symm.trans hx), .err (.same rfl), hμ₁⟩
  | exnCaseErr hs ihs =>
    cases ho with
    | exnCase hos hoh hom =>
      obtain ⟨rs', μ₁', hs', hrs, hμ₁⟩ := lift_bwd hs ihs hσ hB hos hρ hμ
      cases hrs with
      | err hk => exact ⟨_, _, .exnCaseErr hs', .err hk, hμ₁⟩

/-- If `e` gives `r`, an optimised version of `e`, run in related environments and
    stores, gives an outcome related to `r`. -/
theorem sim_fwd {H : Hints A} {ρ : Env} {μ μ₁ : Store} {e : Expr} {r : Outcome}
    (h : Eval ρ μ e r μ₁) : FwdSim H (Optimizes H) ρ μ e r μ₁ :=
  lift_fwd h (sim_fwd_step h)

/-- If an optimised version of `e` gives `r'`, `e`, run in related environments and
    stores, gives an outcome related to `r'`. -/
theorem sim_bwd {H : Hints A} {ρ' : Env} {μ' μ₁' : Store} {e' : Expr} {r' : Outcome}
    (h : Eval ρ' μ' e' r' μ₁') : BwdSim H (Optimizes H) ρ' μ' e' r' μ₁' := by
  intro σ e ρ μ hσ hB ho hρ hμ
  exact lift_bwd h (sim_bwd_step h) hσ hB ho hρ hμ

/-! ## The theorem -/

/-- **The optimiser preserves the meaning of programs.** -/
theorem optimize_correct (e : Expr) :
    Equiv (inferHints ([] : AEnv A) e) e (optimize ([] : AEnv A) e) := by
  have ho := optimizes_opt (inferHints ([] : AEnv A) e) e []
  constructor
  · intro r μ h
    exact sim_fwd h AEnv.Describes.nil AEnv.Bound.nil ho EnvRel.nil StoreRel.nil
  · intro r' μ' h'
    exact sim_bwd h' AEnv.Describes.nil AEnv.Bound.nil ho EnvRel.nil StoreRel.nil

end Diva.Opt
