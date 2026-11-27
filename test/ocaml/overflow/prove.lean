import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let rec sum n = ...`, with its contract. -/
def sum_fn : RecFun where
  name := "sum"
  f := some "sum"
  x := "n"
  body := (.ite (.binop .le (.var "n") (.int 0)) (.int 0) (.letin "%r" (.binop .add (.var "n") (.app (.var "sum") (.letin "%r" (.binop .sub (.var "n") (.int 1)) (.letin "_" (.assert (.ite (.binop .le (.int (-4611686018427387904)) (.var "%r")) (.binop .le (.var "%r") (.int 4611686018427387903)) (.bool false))) (.var "%r"))))) (.letin "_" (.assert (.ite (.binop .le (.int (-4611686018427387904)) (.var "%r")) (.binop .le (.var "%r") (.int 4611686018427387903)) (.bool false))) (.var "%r"))))
  ρ := []
  spec := {
    pre := fun
      | [arg₀] => ∃ (n : Int), arg₀ = .int n ∧ ((0 ≤ n) ∧ (n ≤ 1000))
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ (n : Int) (r : Int), arg₀ = .int n ∧ res₀ = .int r ∧
        ((0 ≤ r) ∧ (r ≤ (1000 * n)))
      | _, _ => False }

/-- The proof obligation of `sum`. If the proof fails, write one by hand. -/
theorem sum_body : sum_fn.BodyOk .none [] := by
  intro va μ ⟨n, hva, hpre⟩
  subst hva
  simp [sum_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `sum` meets its contract: every call of `sum` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem sum_correct : sum_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, sum_body⟩

/-- `next32`, which has no contract. -/
def next32_val : Value := .clos none "x" (.letin "%r" (.binop .add (.var "x") (.int 1)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) [("sum", sum_fn.clos)]

/-- The obligation of the top-level expression `(let %t2 = (next32 2147483647) in (let %t1 = (sum 10) in (let %r = (%t1 + %t2) in (let _ = (assert (if (-4611686018427387904 <= %r) then (%r <= 4611686018427387903) else false)) in %r))))`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [sum_fn] (.letin "%t2" (.app (.var "next32") (.int 2147483647)) (.letin "%t1" (.app (.var "sum") (.int 10)) (.letin "%r" (.binop .add (.var "%t1") (.var "%t2")) (.letin "_" (.assert (.ite (.binop .le (.int (-4611686018427387904)) (.var "%r")) (.binop .le (.var "%r") (.int 4611686018427387903)) (.bool false))) (.var "%r"))))) (fun _ _ => True) [("next32", next32_val), ("sum", sum_fn.clos)] μ := by
  simp [next32_val, sum_fn, wp, BinOp.denote, Value.isBool, Value.isList, Value.length, Value.lengthNat, Value.isProperList, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(let %t2 = (next32 2147483647) in (let %t1 = (sum 10) in (let %r = (%t1 + %t2) in (let _ = (assert (if (-4611686018427387904 <= %r) then (%r <= 4611686018427387903) else false)) in %r))))` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.letin "%t2" (.app (.var "next32") (.int 2147483647)) (.letin "%t1" (.app (.var "sum") (.int 10)) (.letin "%r" (.binop .add (.var "%t1") (.var "%t2")) (.letin "_" (.assert (.ite (.binop .le (.int (-4611686018427387904)) (.var "%r")) (.binop .le (.var "%r") (.int 4611686018427387903)) (.bool false))) (.var "%r"))))) (fun _ _ => True) [("next32", next32_val), ("sum", sum_fn.clos)] μ :=
  Holds.of_wp (S := .none) (Γ := [sum_fn]) ⟨trivial, sum_body⟩ (top1_wp μ)
