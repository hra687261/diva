import Diva.AbsInt.Domain

open Diva.AbsInt

private def itv (lo hi : Int) : Itv := .range (.fin lo) (.fin hi)

-- interval operations
#guard toString ((itv 0 10).add (itv 1 2))      = "[1, 12]"
#guard toString ((itv 0 10).sub (itv 1 2))      = "[-2, 9]"
#guard toString ((itv (-2) 3).mul (itv 4 5))    = "[-10, 15]"
#guard toString ((itv 0 10).div (Itv.singleton 3))  = "[0, 3]"
#guard toString ((itv 0 10).div (itv (-1) 1))   = "[-∞, +∞]"
#guard toString ((itv 0 100).mod (Itv.singleton 7)) = "[0, 6]"
#guard toString ((itv 0 2).join (itv 5 7))      = "[0, 7]"
#guard toString ((itv 0 5).meet (itv 3 9))      = "[3, 5]"
#guard toString ((itv 0 2).meet (itv 5 7))      = "⊥"

-- widening: a bound that grows goes to infinity, a stable one stays
#guard toString ((itv 0 1).widen (itv 0 2))     = "[0, +∞]"
#guard toString ((itv 0 5).widen (itv 1 3))     = "[0, 5]"

-- comparisons: (may be true, may be false)
#guard Itv.cmpLt (itv 0 3) (itv 5 9)            = (true, false)
#guard Itv.cmpLt (itv 0 6) (itv 5 9)            = (true, true)
#guard Itv.cmpEq (Itv.singleton 2) (Itv.singleton 2)    = (true, false)

-- the empty interval
#guard toString (Itv.bot.join (itv 5 7))        = "[5, 7]"
#guard toString (Itv.bot.add (itv 5 7))         = "⊥"
#guard Itv.bot.leq (itv 5 7)                    = true
#guard toString ((itv 0 5).mul (.range (.fin 2) .posInf)) = "[0, +∞]"

-- narrowing by a comparison
#guard toString (Itv.assumeLt (itv 0 10) (Itv.singleton 5)).1 = "[0, 4]"
#guard toString (Itv.assumeLe (Itv.singleton 5) (itv 0 10)).2 = "[5, 10]"
#guard toString (Itv.assumeLt (itv 5 10) (itv 0 5)).1         = "⊥"
