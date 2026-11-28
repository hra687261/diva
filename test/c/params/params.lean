import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "avg" (.lam "x#0" (.lam "y#1" (.binop .div (.binop .add (.var "x#0") (.var "y#1")) (.int 2)))) (.letin "safe" (.lam "x#2" (.binop .div (.int 100) (.binop .add (.binop .mul (.var "x#2") (.var "x#2")) (.int 1)))) (.letin "inv" (.lam "x#3" (.binop .div (.int 1) (.var "x#3"))) (.letin "main" (.lam "_#4" (.int 0)) (.app (.var "main") .unit)))))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("x#0", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("y#1", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("x#2", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("x#3", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("_#4", { int := .bot, tt := false, ff := false, unit := true, list := false, fn := false, loc := false, ctor := false, len := .bot })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
