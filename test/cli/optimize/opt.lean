import Diva.AbsInt.ItvDomain
import Diva.OptSound

/-! Certificate written by `diva opt --cert`. The theorem `optimized_correct` states
that `optimized` is equivalent to `source`. -/

/-- The program. -/
def source : Diva.Expr :=
  (.letin "width" (.int 8) (.letin "height" (.binop .add (.binop .mul (.var "width") (.int 2)) (.int 4)) (.letin "area" (.binop .mul (.var "width") (.var "height")) (.letin "debug" (.bool false) (.letin "scale" (.lam "x#0" (.ite (.var "debug") (.binop .mul (.var "x#0") (.int 1000)) (.ite (.binop .lt (.var "x#0") (.int 0)) (.int 0) (.binop .add (.binop .mul (.var "x#0") (.int 1)) (.int 0))))) (.letin "clamp" (.lam "x#1" (.ite (.binop .lt (.var "x#1") (.int 0)) (.int 0) (.ite (.binop .lt (.var "x#1") (.int 0)) (.int 1) (.letin "_" (.assert (.binop .ge (.var "x#1") (.int 0))) (.var "x#1"))))) (.binop .add (.app (.var "scale") (.var "area")) (.app (.var "clamp") (.int 3)))))))))

/-- The hints of the analysis. `opt` uses them to choose what to rewrite. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("x#0", { int := (.range (.fin 160) (.fin 160)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot }),
  ("x#1", { int := (.range (.fin 3) (.fin 3)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false, len := .bot })]

/-- The optimised program. -/
def optimized : Diva.Expr :=
  (.letin "scale" (.lam "x#0" (.ite (.binop .lt (.var "x#0") (.int 0)) (.int 0) (.var "x#0"))) (.letin "clamp" (.lam "x#1" (.ite (.binop .lt (.var "x#1") (.int 0)) (.int 0) (.var "x#1"))) (.binop .add (.app (.var "scale") (.int 160)) (.app (.var "clamp") (.int 3)))))

/-- `opt`, run by the kernel with the hints, gives `optimized`. -/
theorem opt_source : Diva.Opt.opt hints true ([] : Diva.AbsInt.AEnv Diva.AbsInt.Itv) source = optimized := by
  decide +kernel

/-- The analysis proves that `source` never fails: the kernel runs `mayFail`. -/
theorem source_safe : Diva.AbsInt.mayFail hints ([] : Diva.AbsInt.AEnv Diva.AbsInt.Itv) source = false := by
  decide +kernel

/-- `optimized` is equivalent to `source`: if one of them gives an outcome, the other
    gives a related outcome, with related stores. Related values are equal, except
    closures, whose bodies may be optimised. The checks are erased: `source` never fails. -/
theorem optimized_correct : Diva.Opt.Equiv hints true source optimized :=
  opt_source ▸ Diva.Opt.opt_erase_correct_of_mayFail hints source source_safe
