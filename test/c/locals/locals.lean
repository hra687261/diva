import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "main" (.lam "_#0" (.letin "x" (.int 3) (.letin "y" (.int 0) (.letin "y" (.letin "%r" (.binop .mul (.var "x") (.int 2)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.letin "x" (.letin "%r" (.binop .add (.var "x") (.var "y")) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.letin "x" (.letin "%r" (.binop .add (.var "x") (.int 1)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.letin "x%2" (.int 100) (.letin "y" (.letin "%r" (.binop .add (.var "y") (.var "x%2")) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.letin "x%2" (.letin "%r" (.binop .sub (.var "x%2") (.int 1)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.letin "%r" (.binop .add (.letin "%r" (.binop .mul (.var "x") (.int 1000)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.var "y")) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r")))))))))))) (.app (.var "main") .unit))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("_#0", { int := .bot, tt := false, ff := false, unit := true, list := false, fn := false, loc := false, ctor := false, len := .bot })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
