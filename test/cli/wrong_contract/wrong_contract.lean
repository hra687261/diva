import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letrec "sum#0" "n#1" (.ite (.binop .le (.var "n#1") (.int 0)) (.int 0) (.binop .add (.var "n#1") (.app (.var "sum#0") (.binop .sub (.var "n#1") (.int 1))))) (.app (.var "sum#0") (.int 10)))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("n#1", { int := (.range (.fin 0) (.fin 10)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false }),
  ("$sum#0", { int := (.range (.fin 0) .posInf), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
