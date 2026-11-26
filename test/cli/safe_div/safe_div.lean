import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  (.letrec "g#0" "n#1" (.lam "x#2" (.ite (.binop .le (.var "n#1") (.int 0)) (.var "x#2") (.app (.app (.var "g#0") (.binop .sub (.var "n#1") (.int 1))) (.binop .add (.binop .mul (.var "x#2") (.var "x#2")) (.int 1))))) (.letin "d" (.app (.app (.var "g#0") (.int 3)) (.int 1)) (.letin "q" (.binop .div (.int 100) (.var "d")) (.letin "pos" (.lam "x#3" (.ite (.binop .gt (.var "x#3") (.int 0)) (.var "x#3") (.int 1))) (.letin "r" (.binop .div (.int 60) (.app (.var "pos") (.binop .sub (.int 0) (.int 5)))) (.binop .add (.var "q") (.var "r")))))))

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("n#1", { int := (.range (.fin 0) (.fin 3)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false }),
  ("$g#0", { int := (.range (.fin 1) .posInf), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false }),
  ("x#2", { int := (.range (.fin 1) .posInf), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false }),
  ("x#3", { int := (.range (.fin (-5)) (.fin (-5))), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false })]

/-- The program never fails, whatever the starting store. -/
theorem program_safe {μ μ' : Diva.Store} {k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
