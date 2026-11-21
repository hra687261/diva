import Diva.Interp
import Diva.Wp

/-!
# Deductive verification: contracts

Each test proves a contract `Triple P e Q` for every input. `triple_of_wp` reduces
it to "`P` implies `wp e Q`". `simp [wp, ...]` computes `wp` into arithmetic, and
`omega` proves it. No proof looks at the rules of `Eval`.

The programs are written as `Expr` terms, because the kernel can't run the parser.
-/

open Diva

/-- The precondition "`x` is an integer `n` such that `p n`". -/
def intIs (x : String) (p : Int → Prop) : Pre :=
  fun ρ _ => ∃ n, ρ.lookup x = some (.int n) ∧ p n

/-- The postcondition "the result is an integer `m` such that `p m`". -/
def resIs (p : Int → Prop) : Post :=
  fun v _ => ∃ m, v = .int m ∧ p m

/-- If `x ≥ 0`, then `x + 1 > 0`. -/
example :
    Triple (intIs "x" (· ≥ 0)) (.binop .add (.var "x") (.int 1)) (resIs (· > 0)) := by
  apply triple_of_wp
  intro ρ μ ⟨n, hx, hn⟩
  simp [wp, hx, BinOp.denote, resIs]
  omega

/-- `abs`: `if x < 0 then 0 - x else x` is at least `0`, and at least `x`, for every
    integer `x`. -/
def absX : Expr :=
  .ite (.binop .lt (.var "x") (.int 0)) (.binop .sub (.int 0) (.var "x")) (.var "x")

example : Triple (intIs "x" (fun _ => True)) absX (resIs (· ≥ 0)) := by
  apply triple_of_wp
  intro ρ μ ⟨n, hx, _⟩
  simp [absX, wp, hx, BinOp.denote, Value.isBool, resIs]
  omega

/-- `max`: `if x < y then y else x` is at least `x` and at least `y`. The
    postcondition talks about the inputs, so the contract is stated for all `a`, `b`
    (called logical variables), with `x = a` and `y = b`. -/
example (a b : Int) :
    Triple (fun ρ _ => ρ.lookup "x" = some (.int a) ∧ ρ.lookup "y" = some (.int b))
      (.ite (.binop .lt (.var "x") (.var "y")) (.var "y") (.var "x"))
      (resIs (fun m => m ≥ a ∧ m ≥ b)) := by
  apply triple_of_wp
  intro ρ μ ⟨hx, hy⟩
  simp [wp, hx, hy, BinOp.denote, Value.isBool, resIs]
  omega

/-- `let y = x + x in assert (y >= x)`: the `assert` holds when `x ≥ 0`. A contract
    with the postcondition `True` says that the program doesn't fail. -/
example :
    Triple (intIs "x" (· ≥ 0))
      (.letin "y" (.binop .add (.var "x") (.var "x"))
        (.assert (.binop .ge (.var "y") (.var "x"))))
      (fun _ _ => True) := by
  apply triple_of_wp
  intro ρ μ ⟨n, hx, hn⟩
  simp [wp, hx, BinOp.denote, List.lookup]
  omega

/-- `100 / (if x > 0 then x else 1)` doesn't divide by zero, for every integer `x`. -/
example :
    Triple (intIs "x" (fun _ => True))
      (.binop .div (.int 100) (.ite (.binop .gt (.var "x") (.int 0)) (.var "x") (.int 1)))
      (fun _ _ => True) := by
  apply triple_of_wp
  intro ρ μ ⟨n, hx, _⟩
  simp [wp, hx, BinOp.denote, Value.isBool]
  omega

/-! ## A wrong contract

`absX > 0` is wrong: `x = 0` gives `0`. The interpreter's run on `x = 0` is a
counterexample, and `eval_sound` turns it into a proof that the contract fails. -/

example : ¬ Triple (intIs "x" (fun _ => True)) absX (resIs (· > 0)) := by
  intro h
  have hrun : Eval [("x", .int 0)] [] absX (.ok (.int 0)) [] := eval_sound (fuel := 10) rfl
  obtain ⟨v, hv, m, hm, hpos⟩ := h [("x", .int 0)] [] ⟨0, rfl, trivial⟩ _ _ hrun
  cases hv
  cases hm
  omega
