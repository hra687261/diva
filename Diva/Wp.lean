import Diva.Triple

/-!
# Weakest preconditions

`wp S Γ e K` (the weakest precondition) is a property of the environment and the
store. If it holds before `e` runs, then every run of `e` gives a value, and `K`
holds after the run (`wp_sound`).

- `S` gives the contracts of the functions defined by `let rec` inside `e`, by name.
- `Γ` lists the functions with a contract that `e` can call, with their contracts.

`K` is about a `Callee`, not only a value: the value of `e`, or a function of `Γ`
after its first arguments. This is how `wp` handles a call `f a₁ ... aₙ` of a
function with `n` parameters. As in OCaml, `f a₁ a₂` is `(f a₁) a₂`, and `f a₁`
gives a closure.
- At the name `f`, `wp` finds `f` in `Γ` by its name: `.start g`.
- Each argument gives the next `Callee`. The last one runs the body: `wp` asks for
  the precondition of `g` on all the arguments, and then assumes its postcondition.
- At `let rec f x = body`, `wp` asks for a proof that `body` meets `f`'s contract.
  The recursive calls in `body` assume that contract.

Assuming a contract at recursive calls is sound because `wp_sound` is proved by
induction on the run: the run of a recursive call is a part of the run of `body`.

To prove `Triple P e Q`, prove that `P` implies `wp S [] e Q` (`triple_of_wp`). For
integer programs, `simp [wp]` then `omega` usually does it.

Supported: literals, names, binary operators, `if`, `let`, `assert`, calls of the
functions of `Γ` with all their arguments, and `let rec` with one parameter. On any
other construct, `wp` is `False`.
-/

namespace Diva

/-- The contract of a function: `pre` on the arguments, and `post` on the arguments
    and the result. -/
structure FunSpec where
  pre : List Value → Prop
  post : List Value → Value → Prop

/-- The contracts of the functions defined by `let rec`, by function name. -/
abbrev Contracts := String → Option FunSpec

/-- No function has a contract. -/
def Contracts.none : Contracts := fun _ => Option.none

/-- A function named `name`, with the parameters `x` and `rest`, defined in the
    environment `ρ`, with its contract `spec`. `f` is `some name` for
    `let rec name x ... = body`, and `none` for `let name x ... = body` (a function
    that can't call itself). `let f x y = body` is `let f x = fun y -> body`. -/
structure RecFun where
  name : String
  f : Option String
  x : String
  rest : List String := []
  body : Expr
  ρ : Env
  spec : FunSpec

/-- The value of the function `g`: its closure. -/
def RecFun.clos (g : RecFun) : Value := .clos g.f g.x (lams g.rest g.body) g.ρ

/-- The environment in which a call of `g` on its first argument `v` runs. -/
@[simp] def RecFun.env₁ (g : RecFun) (v : Value) : Env :=
  callEnv g.f g.x (lams g.rest g.body) g.ρ v

/-- What `wp` knows about a function value at a call. -/
inductive Callee where
  /-- The function `g` of `Γ`, before its first argument. -/
  | start : RecFun → Callee
  /-- The function `g` after the arguments `vs`. Its closure waits for the parameter
      `p`, in the environment `E`. `ps` are the parameters after `p`. -/
  | after : RecFun → List Value → Env → String → List String → Callee
  /-- Any value. -/
  | val : Value → Callee

/-- The value of `c`. -/
@[simp] def Callee.value : Callee → Value
  | .start g => g.clos
  | .after g _ E p ps => .clos none p (lams ps g.body) E
  | .val v => v

/-- A postcondition on a `Callee`. -/
abbrev CPost := Callee → Store → Prop

/-- What a call needs so that `K` holds after it. The call gave `g` the arguments
    `vs`, and its environment is `E`. `ps` are the parameters of `g` that have no
    argument yet.
    - If `ps` is empty, the call runs the body of `g`. The arguments must satisfy the
      precondition, and the postcondition must give `K`.
    - Otherwise, the call gives the closure that waits for the next argument. -/
@[simp] def RecFun.stepResult (g : RecFun) (vs : List Value) (E : Env) (K : CPost)
    (μ : Store) : List String → Prop
  | [] => g.spec.pre vs ∧ ∀ v μ', g.spec.post vs v → K (.val v) μ'
  | p :: ps => K (.after g vs E p ps) μ

/-- What the call of `c` on the argument `va` needs, so that `K` holds after it.
    Only a function of `Γ` can be called. -/
@[simp] def Callee.step (va : Value) (K : CPost) (μ : Store) : Callee → Prop
  | .start g => g.stepResult [va] (g.env₁ va) K μ g.rest
  | .after g vs E p ps => g.stepResult (vs ++ [va]) ((p, va) :: E) K μ ps
  | .val _ => False

/-- The weakest precondition of `e` for the postcondition `K`, from `ρ` and `μ`. `Γ`
    lists the functions with a contract that `e` can call, innermost first. -/
def wp (S : Contracts) : List RecFun → Expr → CPost → Env → Store → Prop
  | _, .int n, K, _, μ => K (.val (.int n)) μ
  | _, .bool b, K, _, μ => K (.val (.bool b)) μ
  | _, .unit, K, _, μ => K (.val .unit) μ
  -- a function of `Γ`, found by its name, or any other value
  | Γ, .var x, K, ρ, μ =>
    match Γ.find? (·.name == x) with
    | some g => ρ.lookup x = some g.clos ∧ K (.start g) μ
    | none => ∃ v, ρ.lookup x = some v ∧ K (.val v) μ
  | Γ, .binop op a b, K, ρ, μ =>
    wp S Γ a (fun ca μ₁ =>
      wp S Γ b (fun cb μ₂ => ∃ v, op.denote ca.value cb.value = .ok v ∧ K (.val v) μ₂)
        ρ μ₁) ρ μ
  | Γ, .ite c t e, K, ρ, μ =>
    wp S Γ c (fun cc μ₁ => cc.value.isBool = true ∧
      (cc.value = .bool true → wp S Γ t K ρ μ₁) ∧
      (cc.value = .bool false → wp S Γ e K ρ μ₁)) ρ μ
  | Γ, .letin x a b, K, ρ, μ =>
    wp S Γ a (fun ca μ₁ => wp S Γ b K ((x, ca.value) :: ρ) μ₁) ρ μ
  | Γ, .assert c, K, ρ, μ =>
    wp S Γ c (fun cc μ₁ => cc.value = .bool true ∧ K (.val .unit) μ₁) ρ μ
  -- `f` has a contract `sp`. The body meets it, assuming it at recursive calls. Then
  -- `e₂` runs with `f` defined. Here `f` has one parameter.
  | Γ, .letrec f x body e₂, K, ρ, μ =>
    ∃ sp, S f = some sp ∧ -- There exists a contract `sp` for `f`
      (∀ va μ₁, sp.pre [va] →
        wp S (⟨f, some f, x, [], body, ρ, sp⟩ :: Γ) body (fun c _ => sp.post [va] c.value)
          (callEnv (some f) x body ρ va) μ₁) ∧
      -- body meets the `f`'s contract `sp`
      -- `f` is added to `Γ` for recursive calls
      -- `μ₁` is any store because the function can be called with any store
      wp S (⟨f, some f, x, [], body, ρ, sp⟩ :: Γ) e₂ K ((f, .clos (some f) x body ρ) :: ρ) μ
  -- the call of what `fn` gives, on what `a` gives (`Callee.step`)
  | Γ, .app fn a, K, ρ, μ =>
    wp S Γ fn (fun cf μ₁ => wp S Γ a (fun ca μ₂ => cf.step ca.value K μ₂) ρ μ₁) ρ μ
  | _, _, _, _, _ => False

/-- The proof obligation of `g`, after the arguments `vs`, in the environment `E`. `ps`
    are the parameters that have no argument yet. For all their arguments, if all the
    arguments satisfy the precondition of `g`, the body of `g` satisfies `wp` for the
    postcondition of `g`. Calls in the body assume the contracts of `g` and of `Γ`, the
    functions defined before `g`. -/
def RecFun.BodyFrom (g : RecFun) (S : Contracts) (Γ : List RecFun) :
    List Value → Env → List String → Prop
  | vs, E, [] => ∀ μ, g.spec.pre vs →
    wp S (g :: Γ) g.body (fun c _ => g.spec.post vs c.value) E μ
  | vs, E, p :: ps => ∀ v, g.BodyFrom S Γ (vs ++ [v]) ((p, v) :: E) ps

/-- The proof obligation of `g`: `BodyFrom` for every first argument `v`. -/
def RecFun.BodyOk (g : RecFun) (S : Contracts) (Γ : List RecFun) : Prop :=
  ∀ v, g.BodyFrom S Γ [v] (g.env₁ v) g.rest

/-- Every function `g` of `Γ` meets its contract: its body satisfies `wp` for its
    contract. In that `wp`, the calls in the body of `g` can use the contract of `g`
    (recursive calls) and the contracts of the functions defined before `g`. -/
def Verified (S : Contracts) : List RecFun → Prop
  | [] => True
  | g :: Γ => Verified S Γ ∧ g.BodyOk S Γ

/-- A function `g` of `Γ` meets its contract, with the functions defined before it. -/
theorem Verified.of_mem {S : Contracts} {g : RecFun} :
    ∀ {Γ : List RecFun}, Verified S Γ → g ∈ Γ → ∃ Γ', Verified S (g :: Γ')
  | [], _, hg => by cases hg
  | g' :: Γ, hv, hg => by
    cases hg with
    | head => exact ⟨Γ, hv⟩
    | tail _ hg => exact Verified.of_mem hv.1 hg

/-- What `wp_sound` knows about a `Callee` that a run gives. For a function `g` after
    some arguments, `g` meets its contract, and its obligation holds after these
    arguments. -/
def Callee.Valid (S : Contracts) : Callee → Prop
  | .start g => ∃ Γ', Verified S (g :: Γ')
  | .after g vs E p ps => ∃ Γ', Verified S (g :: Γ') ∧ g.BodyFrom S Γ' vs E (p :: ps)
  | .val _ => True

/-- A call that gives `g` its arguments `vs`, in the environment `E`, with the
    parameters `ps` still without an argument, runs `b = lams ps g.body` in `E`. If
    `stepResult` holds, the run gives a `Callee` for which `K` holds.
    - If `ps` is empty, `b` is the body of `g`. `ihb` is `wp_sound` for its run.
    - Otherwise, `b` is a `fun`, and its run gives a closure. -/
theorem RecFun.stepResult_sound {S : Contracts} {g : RecFun} {Γ : List RecFun}
    {K : CPost} {vs : List Value} {E : Env} {μ μ' : Store} {b : Expr} {r : Outcome} :
    ∀ {ps : List String}, b = lams ps g.body → Eval E μ b r μ' →
    (∀ Γ K, Verified S Γ → wp S Γ b K E μ →
      ∃ c : Callee, r = .ok c.value ∧ c.Valid S ∧ K c μ') →
    Verified S (g :: Γ) → g.BodyFrom S Γ vs E ps → g.stepResult vs E K μ ps →
    ∃ c : Callee, r = .ok c.value ∧ c.Valid S ∧ K c μ'
  | [], hb, _, ihb, hv, hfrom, hstep => by
    obtain ⟨hpre, hpost⟩ := hstep
    subst hb
    obtain ⟨c, rc, _, hq⟩ := ihb (g :: Γ) _ hv (hfrom μ hpre)
    exact ⟨.val c.value, rc, trivial, hpost _ μ' hq⟩
  | p :: ps, hb, he, _, hv, hfrom, hstep => by
    subst hb
    -- `b` is `fun p -> ...`: its run gives its closure, and doesn't change the store
    cases he
    exact ⟨.after g vs E p ps, rfl, ⟨Γ, hv, hfrom⟩, hstep⟩

/-- `Outcome.ok v = .ok c.value` gives `c.value = v`. -/
theorem Callee.value_of_ok {v : Value} {c : Callee} (h : Outcome.ok v = .ok c.value) :
    c.value = v := by
  injection h with h
  exact h.symm

/-- **`wp` is sound**: if `wp S Γ e K ρ μ` holds and the functions of `Γ` meet their
    contracts, the run of `e` gives a value, and `K` holds for a `Callee` of that
    value. By induction on the run, so the run of a recursive call is covered by the
    induction hypothesis. -/
theorem wp_sound {S : Contracts} {ρ : Env} {μ : Store} {e : Expr} {r : Outcome}
    {μ' : Store} (h : Eval ρ μ e r μ') :
    ∀ Γ K, Verified S Γ → wp S Γ e K ρ μ →
      ∃ c : Callee, r = .ok c.value ∧ c.Valid S ∧ K c μ' := by
  induction h with
  | int | bool | unit =>
    intro Γ K _ hw
    exact ⟨.val _, rfl, trivial, hw⟩
  | @var v _ _ x hl =>
    intro Γ K hv hw
    cases hfind : Γ.find? (·.name == x) with
    | none =>
      simp only [wp, hfind] at hw
      obtain ⟨v', hx, hk⟩ := hw
      rw [hl] at hx
      cases hx
      exact ⟨.val v, rfl, trivial, hk⟩
    | some g =>
      -- `x` is the name of the function `g` of `Γ`
      simp only [wp, hfind] at hw
      obtain ⟨hx, hk⟩ := hw
      rw [hl] at hx
      cases hx
      have hg : g ∈ Γ := List.mem_of_find?_eq_some hfind
      exact ⟨.start g, rfl, Verified.of_mem hv hg, hk⟩
  | @varErr _ _ x hl =>
    intro Γ K _ hw
    cases hfind : Γ.find? (·.name == x) with
    | none =>
      simp only [wp, hfind] at hw
      obtain ⟨v, hx, _⟩ := hw
      rw [hl] at hx
      cases hx
    | some g =>
      simp only [wp, hfind] at hw
      rw [hl] at hw
      cases hw.1
  | binop _ _ iha ihb =>
    intro Γ K hv hw
    obtain ⟨_, ra, _, hb⟩ := iha Γ _ hv hw
    cases ra
    obtain ⟨_, rb, _, v, hd, hq⟩ := ihb Γ _ hv hb
    cases rb
    exact ⟨.val v, hd, trivial, hq⟩
  | binopErrL _ iha =>
    intro Γ K hv hw
    obtain ⟨_, ra, _⟩ := iha Γ _ hv hw
    cases ra
  | binopErrR _ _ iha ihb =>
    intro Γ K hv hw
    obtain ⟨_, ra, _, hb⟩ := iha Γ _ hv hw
    cases ra
    obtain ⟨_, rb, _⟩ := ihb Γ _ hv hb
    cases rb
  | ifT _ _ ihc iht =>
    intro Γ K hv hw
    obtain ⟨cc, rc, _, _, hT, _⟩ := ihc Γ _ hv hw
    exact iht Γ K hv (hT (Callee.value_of_ok rc))
  | ifF _ _ ihc ihe =>
    intro Γ K hv hw
    obtain ⟨cc, rc, _, _, _, hF⟩ := ihc Γ _ hv hw
    exact ihe Γ K hv (hF (Callee.value_of_ok rc))
  | ifNotBool _ hnb ihc =>
    intro Γ K hv hw
    obtain ⟨cc, rc, _, hb, _⟩ := ihc Γ _ hv hw
    rw [Callee.value_of_ok rc] at hb
    rw [hb] at hnb
    cases hnb
  | ifErr _ ihc =>
    intro Γ K hv hw
    obtain ⟨_, rc, _⟩ := ihc Γ _ hv hw
    cases rc
  | letin _ _ iha ihb =>
    intro Γ K hv hw
    obtain ⟨_, ra, _, hb⟩ := iha Γ _ hv hw
    cases ra
    exact ihb Γ K hv hb
  | letinErr _ iha =>
    intro Γ K hv hw
    obtain ⟨_, ra, _⟩ := iha Γ _ hv hw
    cases ra
  | assert _ ihc =>
    intro Γ K hv hw
    obtain ⟨_, _, _, _, hq⟩ := ihc Γ _ hv hw
    exact ⟨.val .unit, rfl, trivial, hq⟩
  | assertF _ ihc =>
    intro Γ K hv hw
    obtain ⟨cc, rc, _, ht, _⟩ := ihc Γ _ hv hw
    rw [Callee.value_of_ok rc] at ht
    cases ht
  | assertNotBool _ hnb ihc =>
    intro Γ K hv hw
    obtain ⟨cc, rc, _, ht, _⟩ := ihc Γ _ hv hw
    rw [Callee.value_of_ok rc] at ht
    rw [ht] at hnb
    cases hnb
  | assertErr _ ihc =>
    intro Γ K hv hw
    obtain ⟨_, rc, _⟩ := ihc Γ _ hv hw
    cases rc
  | @letrec f x body ρ _ _ _ _ _ ih =>
    intro Γ K hv hw
    obtain ⟨sp, _, hbody, he⟩ := hw
    -- `f` meets its contract, so `Γ` with `f` is verified
    have hv' : Verified S (⟨f, some f, x, [], body, ρ, sp⟩ :: Γ) := ⟨hv, hbody⟩
    exact ih _ K hv' he
  | app _ _ hb ihf iha ihb =>
    intro Γ K hv hw
    obtain ⟨cf, rf, hvalid, ha⟩ := ihf Γ _ hv hw
    obtain ⟨_, ra, _, hstep⟩ := iha Γ _ hv ha
    cases ra
    -- the called value is a function `g` of `Γ`, after some arguments (`Callee`)
    cases cf with
    | start g =>
      have hclos := Callee.value_of_ok rf
      simp only [Callee.value, RecFun.clos, Value.clos.injEq] at hclos
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hclos
      obtain ⟨Γ', hv'⟩ := hvalid
      exact RecFun.stepResult_sound rfl hb ihb hv' (hv'.2 _) hstep
    | after g vs E p ps =>
      have hclos := Callee.value_of_ok rf
      simp only [Callee.value, Value.clos.injEq] at hclos
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hclos
      obtain ⟨Γ', hv', hfrom⟩ := hvalid
      exact RecFun.stepResult_sound rfl hb ihb hv' (hfrom _) hstep
    | val v =>
      cases hstep
  | appNotFn _ hnf _ ihf iha =>
    intro Γ K hv hw
    obtain ⟨cf, rf, _, ha⟩ := ihf Γ _ hv hw
    obtain ⟨_, ra, _, hstep⟩ := iha Γ _ hv ha
    rw [← Callee.value_of_ok rf] at hnf
    -- the called value is a function of `Γ`, so it is a closure
    cases cf with
    | start g => cases hnf
    | after g vs E p ps => cases hnf
    | val v => cases hstep
  | appErrF _ ihf =>
    intro Γ K hv hw
    obtain ⟨_, rf, _⟩ := ihf Γ _ hv hw
    cases rf
  | appErrA _ _ ihf iha =>
    intro Γ K hv hw
    obtain ⟨_, rf, _, ha⟩ := ihf Γ _ hv hw
    obtain ⟨_, ra, _⟩ := iha Γ _ hv ha
    cases ra
  | _ =>
    intro Γ K _ hw
    simp [wp] at hw

/-- `if c then .err k else .ok v` is `.ok w` exactly when `c` is false and `v = w`.
    `BinOp.denote .div` is `if y = 0 then .err .divZero else .ok ...`, so with this
    lemma `simp` turns "the division gives a value" into "the divisor isn't `0`". -/
@[simp] theorem ite_err_eq_ok {c : Prop} [Decidable c] {k : Err} {v w : Value} :
    ((if c then Outcome.err k else Outcome.ok v) = Outcome.ok w) ↔ (¬ c ∧ v = w) := by
  by_cases hc : c
  case pos => simp [hc]
  case neg => simp [hc]

/-- `∃ v, (P ∧ a = v) ∧ Q v` is `P ∧ Q a`. A division gives this shape after `simp`:
    `P` says that the divisor isn't `0` (`ite_err_eq_ok`), and `a` is the quotient.
    `simp` can't remove `v` by itself, because `a = v` is inside a conjunction. -/
@[simp] theorem exists_and_eq_and {α : Type} {P : Prop} {a : α} {Q : α → Prop} :
    (∃ v, (P ∧ a = v) ∧ Q v) ↔ P ∧ Q a := by
  constructor
  case mp =>
    intro h
    obtain ⟨v, ⟨hp, hv⟩, hq⟩ := h
    subst hv
    exact ⟨hp, hq⟩
  case mpr =>
    intro h
    exact ⟨a, ⟨h.1, rfl⟩, h.2⟩

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
/-- Prove a goal of integer arithmetic made of `∧`, `→` and `∀`, such as the goals that
    `simp [wp]` leaves: introduce the hypotheses and the names, split each `∧`, then
    run `omega` on each part. `repeat'` splits every goal, not only the first one. -/
macro "split_omega" : tactic =>
  `(tactic| (repeat' (first | (intro) | (apply And.intro))) <;> omega)

/-- A contract holds if its precondition implies the weakest precondition, with the
    contracts `S` of the functions defined by `let rec`. -/
theorem triple_of_wp (S : Contracts) {P : Pre} {e : Expr} {Q : Post}
    (h : ∀ ρ μ, P ρ μ → wp S [] e (fun c μ => Q c.value μ) ρ μ) : Triple P e Q := by
  intro ρ μ hp r μ' he
  obtain ⟨c, rc, _, hq⟩ := wp_sound he [] _ trivial (h ρ μ hp)
  exact ⟨c.value, rc, hq⟩

/-- If the functions `Γ` meet their contracts and `wp` holds for `e` from `ρ` and `μ`,
    every run of `e` gives a value that satisfies `Q`. In particular, `e` doesn't
    fail. To prove `wp` for `e`, each call in `e` must get arguments that satisfy the
    precondition of the function that it calls. -/
theorem Holds.of_wp {S : Contracts} {Γ : List RecFun} {e : Expr} {Q : Post} {ρ : Env}
    {μ : Store} (hv : Verified S Γ) (h : wp S Γ e (fun c μ => Q c.value μ) ρ μ) :
    Holds e Q ρ μ := by
  intro r μ' he
  obtain ⟨c, rc, _, hq⟩ := wp_sound he Γ _ hv h
  exact ⟨c.value, rc, hq⟩

/-- `g` meets its contract, after the arguments `vs`, in the environment `E`. `ps` are
    the parameters that have no argument yet. For all their arguments, if all the
    arguments satisfy the precondition of `g`, the run of the body of `g` gives a value
    that satisfies the postcondition of `g`. -/
def RecFun.MeetsFrom (g : RecFun) : List Value → Env → List String → Prop
  | vs, E, [] => ∀ μ, g.spec.pre vs → Holds g.body (fun v _ => g.spec.post vs v) E μ
  | vs, E, p :: ps => ∀ v, g.MeetsFrom (vs ++ [v]) ((p, v) :: E) ps

/-- The function `g` meets its contract: a call of `g` on arguments that satisfy its
    precondition gives a value that satisfies its postcondition. A call of `g` on its
    first argument `v` runs in `g.env₁ v` (`Eval.app`). Each next argument is added
    to that environment. -/
def RecFun.Meets (g : RecFun) : Prop :=
  ∀ v, g.MeetsFrom [v] (g.env₁ v) g.rest

/-- The obligation of `g` after the arguments `vs` (`BodyFrom`) gives `MeetsFrom`. -/
theorem RecFun.meetsFrom_of_bodyFrom {S : Contracts} {g : RecFun} {Γ : List RecFun}
    (h : Verified S (g :: Γ)) :
    ∀ {ps : List String} {vs : List Value} {E : Env},
    g.BodyFrom S Γ vs E ps → g.MeetsFrom vs E ps
  | [], _, _, hfrom => by
    intro μ hpre r μ' he
    obtain ⟨c, rc, _, hq⟩ := wp_sound he (g :: Γ) _ h (hfrom μ hpre)
    exact ⟨c.value, rc, hq⟩
  | p :: ps, vs, E, hfrom => by
    intro v
    exact meetsFrom_of_bodyFrom h (hfrom v)

/-- If the proof obligations of `g` and of the functions `Γ` defined before `g` hold,
    then `g` meets its contract. -/
theorem RecFun.meets_of_verified {S : Contracts} {g : RecFun} {Γ : List RecFun}
    (h : Verified S (g :: Γ)) : g.Meets := by
  intro v
  exact meetsFrom_of_bodyFrom h (h.2 v)

end Diva
