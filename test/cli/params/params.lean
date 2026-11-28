import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letrec "mul#0" "a#1" (.lam "b#2" (.letin "_" (.assert (.binop .ge (.var "a#1") (.int 0))) (.ite (.binop .le (.var "b#2") (.int 0)) (.int 0) (.binop .add (.var "a#1") (.app (.app (.var "mul#0") (.var "a#1")) (.binop .sub (.var "b#2") (.int 1))))))) (.letin "max" (.lam "a#3" (.lam "b#4" (.ite (.binop .lt (.var "a#3") (.var "b#4")) (.var "b#4") (.var "a#3")))) (.letin "max3" (.lam "a#5" (.lam "b#6" (.lam "c#7" (.app (.app (.var "max") (.app (.app (.var "max") (.var "a#5")) (.var "b#6"))) (.var "c#7"))))) (.letin "area" (.lam "w#8" (.lam "h#9" (.app (.app (.var "mul#0") (.app (.app (.var "max") (.var "w#8")) (.int 0))) (.var "h#9")))) (.app (.app (.var "area") (.app (.app (.app (.var "max3") (.int 1)) (.int 5)) (.int 2))) (.int 3))))))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("a#1", { int := (.range (.fin 1) (.fin 5)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("$mul#0", { int := (.range (.fin 0) .posInf), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("b#2", { int := (.range (.fin 0) (.fin 3)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("a#3", { int := (.range (.fin 1) (.fin 5)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("b#4", { int := (.range (.fin 0) (.fin 5)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("a#5", { int := (.range (.fin 1) (.fin 1)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("b#6", { int := (.range (.fin 5) (.fin 5)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("c#7", { int := (.range (.fin 2) (.fin 2)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("w#8", { int := (.range (.fin 1) (.fin 5)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("h#9", { int := (.range (.fin 3) (.fin 3)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
