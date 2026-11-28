import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "big" (.lam "x#0" (.lam "y#1" (.ite (.ite (.binop .gt (.var "y#1") (.int 0)) (.binop .gt (.letin "%r" (.binop .div (.var "x#0") (.var "y#1")) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.int 1)) (.bool false)) (.int 1) (.int 0)))) (.letin "max" (.lam "a#2" (.lam "b#3" (.ite (.binop .gt (.var "a#2") (.var "b#3")) (.var "a#2") (.var "b#3")))) (.letin "sign" (.lam "x#4" (.ite (.binop .lt (.var "x#4") (.int 0)) (.letin "%r" (.binop .sub (.int 0) (.int 1)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.ite (.binop .gt (.var "x#4") (.int 0)) (.int 1) (.int 0)))) (.letin "main" (.lam "_#5" (.letin "%r" (.binop .add (.letin "%r" (.binop .add (.letin "%r" (.binop .add (.letin "%r" (.binop .mul (.ite (.binop .gt (.int 7) (.int 3)) (.int 1) (.int 0)) (.int 100)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.letin "%r" (.binop .mul (.ite (.binop .gt (.int 4) (.int 9)) (.int 4) (.int 9)) (.int 10)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r")))) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.ite (.ite (.binop .ne (.int 0) (.int 0)) (.bool false) (.bool true)) (.int 1) (.int 0))) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.ite (.ite (.binop .ne (.int 0) (.int 0)) (.binop .ne (.letin "%r" (.binop .div (.int 1) (.int 0)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.int 0)) (.bool false)) (.int 1) (.int 0))) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r")))) (.app (.var "main") .unit)))))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("x#0", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("y#1", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("a#2", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("b#3", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("x#4", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("_#5", { int := .bot, tt := false, ff := false, unit := true, list := false, fn := false, loc := false, ctor := false, len := .bot })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
