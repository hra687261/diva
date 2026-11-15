import Diva.Parser
import Diva.AbsInt.ItvDomain
import Diva.AbsInt.Aeval

open Diva Diva.AbsInt

private def itv (lo hi : Int) : Itv := .range (.fin lo) (.fin hi)

/-- Analyse `s` with `x ∈ [0, 10]`. -/
private def analyse (s : String) : Option String :=
  (Diva.parse s).toOption.map fun e =>
    toString (aeval ([("x", itv 0 10)] : AEnv Itv) e)

#guard analyse "x + 1"                         = some "[1, 11]"
#guard analyse "2 * x - 3"                     = some "[-3, 17]"
#guard analyse "let y = x * x in y + 1"        = some "[1, 101]"
#guard analyse "x / 2"                         = some "[0, 5]"
#guard analyse "x mod 3"                       = some "[0, 2]"
#guard analyse "if x < 5 then 0 else 100"      = some "[0, 100]"
#guard analyse "y"                             = some "[-∞, +∞]"  -- unknown variable
#guard analyse "let x = 7 in x"                = some "7"         -- shadowing
#guard analyse "(fun y -> y) 3"                = some "[-∞, +∞]"  -- not analysed yet
