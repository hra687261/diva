import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `length`, which has no contract. -/
def length_val : Value := .clos (some "length") "%t1" (.matchList (.var "%t1") (.int 0) "_" "t" (.binop .add (.int 1) (.app (.var "length") (.var "t")))) []

/-- `head`, which has no contract. -/
def head_val : Value := .clos none "l" (.matchList (.var "l") (.raise (.exn "Empty" .unit)) "x" "_" (.var "x")) [("length", length_val)]

/-- `safe_head`, which has no contract. -/
def safe_head_val : Value := .clos none "l" (.tryw (.app (.var "head") (.var "l")) "%exn" (.exnCase (.var "%exn") "Empty" "_" (.int 0) (.raise (.var "%exn")))) [("head", head_val), ("length", length_val)]

/-- `sum_to`, which has no contract. -/
def sum_to_val : Value := .clos none "n" (.letin "s" (.ref 0 (.int 0)) (.letin "_" (.letin "%lo" (.int 1) (.letin "%hi" (.var "n") (.letrec "%for" "i" (.ite (.binop .le (.var "i") (.var "%hi")) (.letin "_" (.assign (.var "s") (.binop .add (.deref (.var "s")) (.var "i"))) (.app (.var "%for") (.binop .add (.var "i") (.int 1)))) .unit) (.app (.var "%for") (.var "%lo"))))) (.deref (.var "s")))) [("safe_head", safe_head_val), ("head", head_val), ("length", length_val)]

/-- `let rec fact n = ...`, with its contract. -/
def fact_fn : RecFun where
  name := "fact"
  f := some "fact"
  x := "n"
  body := (.ite (.binop .le (.var "n") (.int 1)) (.int 1) (.binop .mul (.var "n") (.app (.var "fact") (.binop .sub (.var "n") (.int 1)))))
  ρ := [("sum_to", sum_to_val), ("safe_head", safe_head_val), ("head", head_val), ("length", length_val)]
  spec := {
    pre := fun
      | [arg₀] => ∃ n : Int, arg₀ = .int n ∧ (n ≥ 0)
      | _ => False
    post := fun
      | [arg₀], res₀ => ∃ n result : Int, arg₀ = .int n ∧ res₀ = .int result ∧
        True
      | _, _ => False }

/-- The proof obligation of `fact`. If the proof fails, write one by hand. -/
theorem fact_body : fact_fn.BodyOk .none [] := by
  intro va μ ⟨n, hva, hpre⟩
  subst hva
  simp [fact_fn, sum_to_val, safe_head_val, head_val, length_val, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `fact` meets its contract: every call of `fact` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem fact_correct : fact_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, fact_body⟩

/-- The obligation of the top-level expression `(let l = (1 :: (2 :: (3 :: []))) in (let _ = (let _ = (let %t7 = (fact 5) in (let %t6 = (let %t5 = (sum_to 4) in (let %t4 = (let %t3 = (safe_head []) in (let %t2 = (length l) in (%t2 + %t3))) in (%t4 + %t5))) in (%t6 + %t7))) in ()) in (let _ = (let _ = () in ()) in (if (97 <> 97) then (raise Failure) else ()))))`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top1_wp (μ : Store) :
    wp .none [fact_fn] (.letin "l" (.cons (.int 1) (.cons (.int 2) (.cons (.int 3) .nil))) (.letin "_" (.letin "_" (.letin "%t7" (.app (.var "fact") (.int 5)) (.letin "%t6" (.letin "%t5" (.app (.var "sum_to") (.int 4)) (.letin "%t4" (.letin "%t3" (.app (.var "safe_head") .nil) (.letin "%t2" (.app (.var "length") (.var "l")) (.binop .add (.var "%t2") (.var "%t3")))) (.binop .add (.var "%t4") (.var "%t5")))) (.binop .add (.var "%t6") (.var "%t7")))) .unit) (.letin "_" (.letin "_" .unit .unit) (.ite (.binop .ne (.int 97) (.int 97)) (.raise (.exn "Failure" .unit)) .unit)))) (fun _ _ => True) [("fact", fact_fn.clos), ("sum_to", sum_to_val), ("safe_head", safe_head_val), ("head", head_val), ("length", length_val)] μ := by
  simp [fact_fn, sum_to_val, safe_head_val, head_val, length_val, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- The top-level expression `(let l = (1 :: (2 :: (3 :: []))) in (let _ = (let _ = (let %t7 = (fact 5) in (let %t6 = (let %t5 = (sum_to 4) in (let %t4 = (let %t3 = (safe_head []) in (let %t2 = (length l) in (%t2 + %t3))) in (%t4 + %t5))) in (%t6 + %t7))) in ()) in (let _ = (let _ = () in ()) in (if (97 <> 97) then (raise Failure) else ()))))` runs without error. -/
theorem top1_safe (μ : Store) : Holds (.letin "l" (.cons (.int 1) (.cons (.int 2) (.cons (.int 3) .nil))) (.letin "_" (.letin "_" (.letin "%t7" (.app (.var "fact") (.int 5)) (.letin "%t6" (.letin "%t5" (.app (.var "sum_to") (.int 4)) (.letin "%t4" (.letin "%t3" (.app (.var "safe_head") .nil) (.letin "%t2" (.app (.var "length") (.var "l")) (.binop .add (.var "%t2") (.var "%t3")))) (.binop .add (.var "%t4") (.var "%t5")))) (.binop .add (.var "%t6") (.var "%t7")))) .unit) (.letin "_" (.letin "_" .unit .unit) (.ite (.binop .ne (.int 97) (.int 97)) (.raise (.exn "Failure" .unit)) .unit)))) (fun _ _ => True) [("fact", fact_fn.clos), ("sum_to", sum_to_val), ("safe_head", safe_head_val), ("head", head_val), ("length", length_val)] μ :=
  Holds.of_wp (S := .none) (Γ := [fact_fn]) ⟨trivial, fact_body⟩ (top1_wp μ)
