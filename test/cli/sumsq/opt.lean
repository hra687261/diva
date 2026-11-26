import Diva.AbsInt.ItvDomain
import Diva.OptSound

/-! Certificate written by `diva opt --cert`. The theorem `optimized_correct` states
that `optimized` is equivalent to `source`. -/

/-- The program. -/
def source : Diva.Expr :=
  (.letrec "sumsq#0" "n#1" (.lam "acc#2" (.letin "_" (.assert (.binop .le (.var "n#1") (.int 10))) (.letin "_" (.assert (.binop .ge (.var "acc#2") (.int 0))) (.ite (.binop .eq (.var "n#1") (.int 0)) (.var "acc#2") (.letin "acc" (.binop .add (.var "acc#2") (.binop .mul (.var "n#1") (.var "n#1"))) (.ite (.binop .lt (.var "acc") (.int 0)) (.int 0) (.app (.app (.var "sumsq#0") (.binop .sub (.var "n#1") (.int 1))) (.var "acc")))))))) (.app (.app (.var "sumsq#0") (.int 10)) (.int 0)))

/-- The hints of the analysis. `opt` uses them to choose what to rewrite. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := [
  ("n#1", { int := (.range .negInf (.fin 10)), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false }),
  ("$sumsq#0", { int := (.range (.fin 0) .posInf), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false }),
  ("acc#2", { int := (.range (.fin 0) .posInf), tt := false, ff := false, unit := false, list := false, fn := false, loc := false, ctor := false })]

/-- The optimised program. -/
def optimized : Diva.Expr :=
  (.letrec "sumsq#0" "n#1" (.lam "acc#2" (.ite (.binop .eq (.var "n#1") (.int 0)) (.var "acc#2") (.letin "acc" (.binop .add (.var "acc#2") (.binop .mul (.var "n#1") (.var "n#1"))) (.app (.app (.var "sumsq#0") (.binop .sub (.var "n#1") (.int 1))) (.var "acc"))))) (.app (.app (.var "sumsq#0") (.int 10)) (.int 0)))

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
