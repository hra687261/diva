import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

/-- `let rec sumsq n acc = ...`, with the contract that the analysis infers (`diva hints`). -/
def sumsq_fn : RecFun where
  name := "sumsq"
  f := some "sumsq"
  x := "n"
  rest := ["acc"]
  body := (.ite (.binop .eq (.var "n") (.int 0)) (.var "acc") (.letin "acc" (.binop .add (.var "acc") (.binop .mul (.var "n") (.var "n"))) (.ite (.binop .lt (.var "acc") (.int 0)) (.int 0) (.app (.app (.var "sumsq") (.binop .sub (.var "n") (.int 1))) (.var "acc")))))
  ρ := []
  spec := {
    pre := fun
      | [arg₀, arg₁] => ∃ n acc : Int, arg₀ = .int n ∧ arg₁ = .int acc ∧ (n ≤ 10) ∧ (acc ≥ 0)
      | _ => False
    post := fun
      | [arg₀, arg₁], res₀ => ∃ n acc result : Int, arg₀ = .int n ∧ arg₁ = .int acc ∧ res₀ = .int result ∧
        (result ≥ 0)
      | _, _ => False }

/-- The proof obligation of `sumsq`. If the proof fails, write one by hand. -/
theorem sumsq_body : sumsq_fn.BodyOk .none [] := by
  intro va₀ va₁ μ ⟨n, acc, hva₀, hva₁, hpre⟩
  subst hva₀ hva₁
  simp [sumsq_fn, wp, BinOp.denote, Value.isBool, List.lookup, callEnv, RecFun.clos]
  all_goals split_omega

/-- `sumsq` meets its contract: every call of `sumsq` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem sumsq_correct : sumsq_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := []) ⟨trivial, sumsq_body⟩
