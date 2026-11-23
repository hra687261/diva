import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "double" (.lam "x#0" (.binop .add (.var "x#0") (.var "x#0"))) (.letin "quad" (.lam "x#1" (.app (.var "double") (.app (.var "double") (.var "x#1")))) (.app (.var "quad") (.int 3))))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("x#0", { int := (.range (.fin 3) .posInf), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false }),
  ("x#1", { int := (.range (.fin 3) (.fin 3)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
