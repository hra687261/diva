import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letin "clamp" (.lam "x#0" (.lam "lo#1" (.lam "hi#2" (.letin "r" (.var "x#0") (.letin "%k" (.lam "r#3" (.var "r#3")) (.ite (.binop .lt (.var "x#0") (.var "lo#1")) (.letin "r" (.var "lo#1") (.app (.var "%k") (.var "r"))) (.letin "%k%2" (.lam "r#4" (.app (.var "%k") (.var "r#4"))) (.ite (.binop .gt (.var "x#0") (.var "hi#2")) (.letin "r" (.var "hi#2") (.app (.var "%k%2") (.var "r"))) (.app (.var "%k%2") (.var "r")))))))))) (.letin "main" (.lam "_#5" (.letin "a" (.int 5) (.letin "b" (.int 0) (.letin "%k%2" (.lam "b#6" (.lam "a#7" (.letin "%k" (.lam "_#8" (.letin "%r" (.binop .add (.letin "%r" (.binop .mul (.var "a#7") (.int 100)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.var "b#6")) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r")))) (.ite (.binop .eq (.var "b#6") (.int 0)) (.letin "%r" (.binop .div (.int 1) (.var "b#6")) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.app (.var "%k") .unit))))) (.ite (.binop .gt (.var "a") (.int 3)) (.letin "b" (.letin "%r" (.binop .mul (.var "a") (.int 2)) (.letin "_" (.assert (.ite (.binop .le (.int (-2147483648)) (.var "%r")) (.binop .le (.var "%r") (.int 2147483647)) (.bool false))) (.var "%r"))) (.letin "a" (.int 1) (.app (.app (.var "%k%2") (.var "b")) (.var "a")))) (.letin "b" (.int 7) (.app (.app (.var "%k%2") (.var "b")) (.var "a")))))))) (.app (.var "main") .unit)))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("x#0", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("lo#1", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("hi#2", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("r#3", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("r#4", { int := .bot, tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("_#5", { int := .bot, tt := false, ff := false, unit := true, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("b#6", { int := (.range (.fin 10) (.fin 10)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("a#7", { int := (.range (.fin 1) (.fin 1)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("_#8", { int := .bot, tt := false, ff := false, unit := true, list := false, fn := false, loc := false, ctor := false, len := .bot })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
