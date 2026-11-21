import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "width" (.int 8) (.letin "height" (.binop .add (.binop .mul (.var "width") (.int 2)) (.int 4)) (.letin "area" (.binop .mul (.var "width") (.var "height")) (.letin "debug" (.bool false) (.letin "scale" (.lam "x#0" (.ite (.var "debug") (.binop .mul (.var "x#0") (.int 1000)) (.ite (.binop .lt (.var "x#0") (.int 0)) (.int 0) (.binop .add (.binop .mul (.var "x#0") (.int 1)) (.int 0))))) (.letin "clamp" (.lam "x#1" (.ite (.binop .lt (.var "x#1") (.int 0)) (.int 0) (.ite (.binop .lt (.var "x#1") (.int 0)) (.int 1) (.letin "_" (.assert (.binop .ge (.var "x#1") (.int 0))) (.var "x#1"))))) (.binop .add (.app (.var "scale") (.var "area")) (.app (.var "clamp") (.int 3)))))))))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("x#0", { int := (.range (.fin 160) (.fin 160)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false }),
  ("x#1", { int := (.range (.fin 3) (.fin 3)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, exn := false })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
