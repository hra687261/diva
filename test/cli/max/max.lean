import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "max" (.lam "a#0" (.lam "b#1" (.ite (.binop .lt (.var "a#0") (.var "b#1")) (.var "b#1") (.var "a#0")))) (.app (.app (.var "max") (.int 1)) (.int 2)))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("a#0", { int := (.range (.fin 1) (.fin 1)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false }),
  ("b#1", { int := (.range (.fin 2) (.fin 2)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
