import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "abs" (.lam "x#0" (.ite (.binop .lt (.var "x#0") (.int 0)) (.binop .sub (.int 0) (.var "x#0")) (.var "x#0"))) (.letin "dist" (.lam "a#1" (.app (.var "abs") (.binop .sub (.var "a#1") (.int 10)))) (.app (.var "dist") (.int 3))))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("x#0", { int := (.range (.fin (-7)) (.fin (-7))), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false }),
  ("a#1", { int := (.range (.fin 3) (.fin 3)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
