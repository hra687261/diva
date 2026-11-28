import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "main" (.lam "_#0" (.binop .add (.binop .sub (.binop .mul (.binop .add (.int 1) (.int 2)) (.int 7)) (.binop .mod (.binop .div (.int 10) (.int 3)) (.int 2))) (.binop .sub (.int 0) (.int 1)))) (.app (.var "main") .unit))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("_#0", { int := .bot, tt := false, ff := false, unit := true, list := false, fn := false, loc := false, ctor := false, len := .bot })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
