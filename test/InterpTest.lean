import Diva.Parser
import Diva.Interp

/-- Parse and run `s`, and return the value. Return `none` on a parse error, a
    stuck program or exhausted fuel. -/
private def run (s : String) : Option String := do
  let e ← (Diva.parse s).toOption
  let v ← Diva.eval 1000 [] e
  return toString v

#guard run "1 + 2 * 3 - 4"                       = some "3"
#guard run "let x = 40 in x + 2"                 = some "42"
#guard run "(fun x -> x * x) 7"                  = some "49"
#guard run "let add = fun x -> fun y -> x + y in add 1 2" = some "3"
#guard run "if 1 < 2 then 10 else 20"            = some "10"
#guard run "3 = 4"                               = some "false"
#guard run "fun x -> x"                          = some "<fun>"
-- lexical scope: the closure keeps `y = 1`
#guard run "let y = 1 in let f = fun x -> x + y in let y = 100 in f 0" = some "1"
-- stuck programs have no value
#guard run "true + 1"                            = none
#guard run "x"                                   = none
#guard run "1 2"                                 = none
