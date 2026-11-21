import Diva.Triple

/-!
# Weakest preconditions

`wp S Γ e Q` (the weakest precondition) is a property of the environment and the
store. If it holds before `e` runs, then every run of `e` gives a value, and `Q`
holds after the run (`wp_sound`).

- `S` gives the contracts of functions, by name.
- `Γ` lists the functions defined by `let rec` so far, with their contracts.

To prove `Triple P e Q`, prove that `P` implies `wp S [] e Q` (`triple_of_wp`). For
integer programs, `simp [wp]` then `omega` usually does it.

Contracts of functions:
- At a call `f a`, `wp` asks for `f`'s precondition on `a`, and then assumes `f`'s
  postcondition on the result.
- At `let rec f x = body`, `wp` asks for a proof that `body` meets `f`'s contract.
  The recursive calls in `body` assume that contract.

Assuming the contract at recursive calls is sound because `wp_sound` is proved by
induction on the run: the run of a recursive call is a part of the run of `body`.

Supported: literals, names, binary operators, `if`, `let`, `assert`, calls, and
`let rec` with one parameter. On any other construct, `wp` is `False`.
-/

namespace Diva

/-- The contract of a function with one parameter: `pre` on the argument, and `post`
    on the argument and the result. -/
structure FunSpec where
  pre : Value → Prop
  post : Value → Value → Prop

/-- The contracts of the functions defined by `let rec`, by function name. -/
abbrev Contracts := String → Option FunSpec

/-- No function has a contract. -/
def Contracts.none : Contracts := fun _ => Option.none

/-- The function defined by `let rec f x = body`, in the environment `ρ`, with its
    contract `spec`. -/
structure RecFun where
  f : String
  x : String
  body : Expr
  ρ : Env
  spec : FunSpec

/-- The value of the function `g`: its closure. -/
def RecFun.clos (g : RecFun) : Value := .clos (some g.f) g.x g.body g.ρ

/-- What a call of the function value `vf` on the argument `va` needs, so that `Q`
    holds after the call: `vf` is the closure of a function `g` of `Γ`, `va`
    satisfies the precondition of `g`, and the postcondition of `g` implies `Q`. -/
@[simp] def callPre (Γ : List RecFun) (Q : Post) (vf va : Value) : Prop :=
  ∃ g ∈ Γ, vf = g.clos ∧ g.spec.pre va ∧ ∀ v μ, g.spec.post va v → Q v μ

/-- The weakest precondition of `e` for the postcondition `Q`, from `ρ` and `μ`. `Γ`
    lists the functions defined so far by `let rec`, innermost first. -/
def wp (S : Contracts) : List RecFun → Expr → Post → Env → Store → Prop
  | _, .int n, Q, _, μ => Q (.int n) μ
  | _, .bool b, Q, _, μ => Q (.bool b) μ
  | _, .unit, Q, _, μ => Q .unit μ
  | _, .var x, Q, ρ, μ => ∃ v, ρ.lookup x = some v ∧ Q v μ
  | Γ, .binop op a b, Q, ρ, μ =>
    wp S Γ a (fun va μ₁ =>
      wp S Γ b (fun vb μ₂ => ∃ v, op.denote va vb = .ok v ∧ Q v μ₂) ρ μ₁) ρ μ
  | Γ, .ite c t e, Q, ρ, μ =>
    wp S Γ c (fun vc μ₁ => vc.isBool = true ∧
      (vc = .bool true → wp S Γ t Q ρ μ₁) ∧ (vc = .bool false → wp S Γ e Q ρ μ₁)) ρ μ
  | Γ, .letin x a b, Q, ρ, μ => wp S Γ a (fun v μ₁ => wp S Γ b Q ((x, v) :: ρ) μ₁) ρ μ
  | Γ, .assert c, Q, ρ, μ => wp S Γ c (fun vc μ₁ => vc = .bool true ∧ Q .unit μ₁) ρ μ
  -- `f` has a contract `sp`. The body meets it, assuming it at recursive calls. Then
  -- `e₂` runs with `f` defined.
  | Γ, .letrec f x body e₂, Q, ρ, μ =>
    ∃ sp, S f = some sp ∧ -- There exists a contract `sp` for `f`
      (∀ va μ₁, sp.pre va →
        wp S (⟨f, x, body, ρ, sp⟩ :: Γ) body (fun v _ => sp.post va v)
          (callEnv (some f) x body ρ va) μ₁) ∧
      -- body meets the `f`'s contract `sp`
      -- `f` is added to `Γ` for recursive calls
      -- `μ₁` is any store because the function can be called with any store
      wp S (⟨f, x, body, ρ, sp⟩ :: Γ) e₂ Q ((f, .clos (some f) x body ρ) :: ρ) μ
  -- the function is one of `Γ`, the argument meets its precondition, and its
  -- postcondition gives `Q`, whatever the store after the call
  | Γ, .app fn a, Q, ρ, μ =>
    let afterFn : Post := fun vf μ₁ => wp S Γ a (fun va _ => callPre Γ Q vf va) ρ μ₁
    wp S Γ fn afterFn ρ μ
  | _, _, _, _, _ => False

/-- Every function `g` of `Γ` meets its contract: its body satisfies `wp` for its
    contract. In that `wp`, the calls in the body of `g` can use the contract of `g`
    (recursive calls) and the contracts of the functions defined before `g`. -/
def Verified (S : Contracts) : List RecFun → Prop
  | [] => True
  | g :: Γ => Verified S Γ ∧ ∀ va μ, g.spec.pre va →
      wp S (g :: Γ) g.body (fun v _ => g.spec.post va v) (callEnv (some g.f) g.x g.body g.ρ va) μ

/-- A function `g` of `Γ` meets its contract, with the functions defined before it. -/
theorem Verified.of_mem {S : Contracts} {g : RecFun} :
    ∀ {Γ : List RecFun}, Verified S Γ → g ∈ Γ → ∃ Γ', Verified S (g :: Γ')
  | [], _, hg => by cases hg
  | g' :: Γ, hv, hg => by
    cases hg with
    | head => exact ⟨Γ, hv⟩
    | tail _ hg => exact Verified.of_mem hv.1 hg

/-- **`wp` is sound**: if `wp S Γ e Q ρ μ` holds and the functions of `Γ` meet their
    contracts, the run of `e` gives a value that satisfies `Q`. By induction on the
    run, so the run of a recursive call is covered by the induction hypothesis. -/
theorem wp_sound {S : Contracts} {ρ : Env} {μ : Store} {e : Expr} {r : Outcome}
    {μ' : Store} (h : Eval ρ μ e r μ') :
    ∀ Γ Q, Verified S Γ → wp S Γ e Q ρ μ → ∃ v, r = .ok v ∧ Q v μ' := by
  induction h with
  | int | bool | unit =>
    intro Γ Q _ hw
    exact ⟨_, rfl, hw⟩
  | var hl =>
    intro Γ Q _ hw
    obtain ⟨v, hx, hq⟩ := hw
    rw [hl] at hx
    cases hx
    exact ⟨_, rfl, hq⟩
  | varErr hl =>
    intro Γ Q _ hw
    obtain ⟨v, hx, _⟩ := hw
    rw [hl] at hx
    cases hx
  | binop _ _ iha ihb =>
    intro Γ Q hv hw
    obtain ⟨_, ra, hb⟩ := iha Γ _ hv hw
    cases ra
    obtain ⟨_, rb, v, hd, hq⟩ := ihb Γ _ hv hb
    cases rb
    exact ⟨v, hd, hq⟩
  | binopErrL _ iha =>
    intro Γ Q hv hw
    obtain ⟨_, ra, _⟩ := iha Γ _ hv hw
    cases ra
  | binopErrR _ _ iha ihb =>
    intro Γ Q hv hw
    obtain ⟨_, ra, hb⟩ := iha Γ _ hv hw
    cases ra
    obtain ⟨_, rb, _⟩ := ihb Γ _ hv hb
    cases rb
  | ifT _ _ ihc iht =>
    intro Γ Q hv hw
    obtain ⟨_, rc, _, hT, _⟩ := ihc Γ _ hv hw
    cases rc
    exact iht Γ Q hv (hT rfl)
  | ifF _ _ ihc ihe =>
    intro Γ Q hv hw
    obtain ⟨_, rc, _, _, hF⟩ := ihc Γ _ hv hw
    cases rc
    exact ihe Γ Q hv (hF rfl)
  | ifNotBool _ hnb ihc =>
    intro Γ Q hv hw
    obtain ⟨_, rc, hb, _⟩ := ihc Γ _ hv hw
    cases rc
    rw [hb] at hnb
    cases hnb
  | ifErr _ ihc =>
    intro Γ Q hv hw
    obtain ⟨_, rc, _⟩ := ihc Γ _ hv hw
    cases rc
  | letin _ _ iha ihb =>
    intro Γ Q hv hw
    obtain ⟨_, ra, hb⟩ := iha Γ _ hv hw
    cases ra
    exact ihb Γ Q hv hb
  | letinErr _ iha =>
    intro Γ Q hv hw
    obtain ⟨_, ra, _⟩ := iha Γ _ hv hw
    cases ra
  | assert _ ihc =>
    intro Γ Q hv hw
    obtain ⟨_, rc, _, hq⟩ := ihc Γ _ hv hw
    cases rc
    exact ⟨_, rfl, hq⟩
  | assertF _ ihc =>
    intro Γ Q hv hw
    obtain ⟨_, rc, ht, _⟩ := ihc Γ _ hv hw
    cases rc
    cases ht
  | assertNotBool _ hnb ihc =>
    intro Γ Q hv hw
    obtain ⟨_, rc, ht, _⟩ := ihc Γ _ hv hw
    cases rc
    rw [ht] at hnb
    cases hnb
  | assertErr _ ihc =>
    intro Γ Q hv hw
    obtain ⟨_, rc, _⟩ := ihc Γ _ hv hw
    cases rc
  | @letrec f x body ρ _ _ _ _ _ ih =>
    intro Γ Q hv hw
    obtain ⟨sp, _, hbody, he⟩ := hw
    -- `f` meets its contract, so `Γ` with `f` is verified
    have hv' : Verified S (⟨f, x, body, ρ, sp⟩ :: Γ) := ⟨hv, hbody⟩
    exact ih _ Q hv' he
  | app _ _ _ ihf iha ihb =>
    intro Γ Q hv hw
    obtain ⟨_, rf, ha⟩ := ihf Γ _ hv hw
    cases rf
    obtain ⟨_, ra, g, hg, hclos, hpre, hpost⟩ := iha Γ _ hv ha
    cases ra
    -- the closure that is called is `g`'s
    cases hclos
    -- `g`'s body meets its contract, with the functions defined before `g`
    obtain ⟨Γ', hv'⟩ := Verified.of_mem hv hg
    obtain ⟨v, rb, hq⟩ := ihb (g :: Γ') _ hv' (hv'.2 _ _ hpre)
    exact ⟨v, rb, hpost v _ hq⟩
  | appNotFn _ hnf _ ihf iha =>
    intro Γ Q hv hw
    obtain ⟨_, rf, ha⟩ := ihf Γ _ hv hw
    cases rf
    obtain ⟨_, ra, g, _, hclos, _⟩ := iha Γ _ hv ha
    cases ra
    -- `g`'s value is a closure
    rw [hclos] at hnf
    cases hnf
  | appErrF _ ihf =>
    intro Γ Q hv hw
    obtain ⟨_, rf, _⟩ := ihf Γ _ hv hw
    cases rf
  | appErrA _ _ ihf iha =>
    intro Γ Q hv hw
    obtain ⟨_, rf, ha⟩ := ihf Γ _ hv hw
    cases rf
    obtain ⟨_, ra, _⟩ := iha Γ _ hv ha
    cases ra
  | _ =>
    intro Γ Q _ hw
    simp [wp] at hw

/-- `if c then .err k else .ok v` is `.ok w` exactly when `c` is false and `v = w`.
    `BinOp.denote .div` is `if y = 0 then .err .divZero else .ok ...`, so with this
    lemma `simp` turns "the division gives a value" into "the divisor isn't `0`". -/
@[simp] theorem ite_err_eq_ok {c : Prop} [Decidable c] {k : Err} {v w : Value} :
    ((if c then Outcome.err k else Outcome.ok v) = Outcome.ok w) ↔ (¬ c ∧ v = w) := by
  by_cases hc : c
  case pos => simp [hc]
  case neg => simp [hc]

/-- `∀ v m, v = .int m → p v m` is `∀ m, p (.int m) m`. A postcondition "the result is
    an integer `m` such that ..." gives this goal shape at calls. `simp` can't
    substitute `v` there by itself, because `m` comes after `v`. -/
@[simp] theorem forall_eq_int {p : Value → Int → Prop} :
    (∀ v m, v = .int m → p v m) ↔ ∀ m, p (.int m) m := by
  constructor
  case mp =>
    intro h m
    exact h _ m rfl
  case mpr =>
    intro h v m hv
    rw [hv]
    exact h m

/-- A contract holds if its precondition implies the weakest precondition, with the
    contracts `S` of the functions defined by `let rec`. -/
theorem triple_of_wp (S : Contracts) {P : Pre} {e : Expr} {Q : Post}
    (h : ∀ ρ μ, P ρ μ → wp S [] e Q ρ μ) : Triple P e Q := by
  intro ρ μ hp r μ' he
  exact wp_sound he [] Q trivial (h ρ μ hp)

end Diva
