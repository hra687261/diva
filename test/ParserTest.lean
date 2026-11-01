import Diva.Parser

/-- Parse `s` and render its tree, or `none` on a parse error. -/
private def parseStr (s : String) : Option String :=
  (Diva.parse s).toOption.map toString

#guard parseStr "1 + 2 * 3 - 4"       = some "((1 + (2 * 3)) - 4)"
#guard parseStr "(1 + 2) * 3"         = some "((1 + 2) * 3)"
#guard parseStr "a - b - c"           = some "((a - b) - c)"
#guard parseStr "a = b"               = some "(a = b)"
#guard parseStr "f x y"               = some "((f x) y)"
#guard parseStr "let x = 40 in x + 2" = some "(let x = 40 in (x + 2))"
#guard parseStr "fun x -> x + 1"      = some "(fun x -> (x + 1))"
#guard parseStr "if a then b else c"  = some "(if a then b else c)"
#guard parseStr "a = b = c"           = none
