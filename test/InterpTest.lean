import Diva.Parser
import Diva.Interp

/-- Parse and run `s`, and return its outcome, a value, an error, or none if out
    of fuel -/
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

-- comparisons
#guard run "3 <> 4"                              = some "true"
#guard run "3 <= 3"                              = some "true"
#guard run "3 > 4"                               = some "false"
#guard run "4 >= 5"                              = some "false"

-- unary minus
#guard run "-3 + 1"                              = some "-2"
#guard run "let x = 5 in -x * 2"                 = some "-10"

-- `=` and `<>` on bools and units
#guard run "true = false"                        = some "false"
#guard run "true <> false"                       = some "true"
#guard run "() = ()"                             = some "true"
#guard run "1 = true"                            = some "error: type error"

-- programs that go wrong evaluate to an error
#guard run "true + 1"                            = some "error: type error"
#guard run "x"                                   = some "error: unbound variable"
#guard run "1 2"                                 = some "error: type error"
#guard run "if 1 then 2 else 3"                  = some "error: type error"
-- errors propagate, left operand first
#guard run "1 / 0 + x"                           = some "error: division by zero"

-- division (truncating, like OCaml)
#guard run "7 / 2"                               = some "3"
#guard run "-7 / 2"                              = some "-3"
#guard run "-7 mod 2"                            = some "-1"
#guard run "1 / 0"                               = some "error: division by zero"
#guard run "5 mod 0"                             = some "error: division by zero"

-- unit and assert
#guard run "()"                                  = some "()"
#guard run "assert (1 < 2)"                      = some "()"
#guard run "assert (2 < 1)"                      = some "error: assertion failed"
#guard run "assert 1"                            = some "error: type error"

-- recursion
#guard run "let rec fact n = if n = 0 then 1 else n * fact (n - 1) in fact 5" = some "120"
#guard run "let rec f = fun n -> if n = 0 then 0 else f (n - 1) in f 3" = some "0"
-- infinite recursion runs out of fuel
#guard run "let rec loop x = loop x in loop 0"   = none

-- surface sugar
#guard run "(fun x y -> x - y) 5 3"              = some "2"
#guard run "let sub x y = x - y in sub 5 3"      = some "2"
#guard run "1 < 2 && 2 < 3"                      = some "true"
#guard run "1 > 2 || 2 < 3"                      = some "true"
#guard run "not (1 = 1)"                         = some "false"
-- `&&` short-circuits: the right side is never evaluated
#guard run "false && 1 / 0 = 0"                  = some "false"
#guard run "assert true; 42"                     = some "42"
#guard run "assert false; 42"                    = some "error: assertion failed"

-- lists
#guard run "1 :: 2 :: []"                        = some "(1 :: (2 :: []))"
#guard run "1 :: 2"                              = some "error: type error"
#guard run "let rec len l = match l with [] -> 0 | x :: xs -> 1 + len xs in len (1 :: 2 :: 3 :: [])" = some "3"
#guard run "match [] with [] -> 0 | x :: xs -> x" = some "0"
#guard run "match [1; 2] with [] -> 0 | x :: xs -> x" = some "1"
#guard run "if 1 < 2 then assert true"           = some "()"
#guard run "match 1 with [] -> 0 | x :: xs -> x" = some "error: type error"

-- top-level declarations
#guard run "let x = 40 let y = 2 ;; x + y"       = some "42"
#guard run "let rec fact n = if n = 0 then 1 else n * fact (n - 1) ;; fact 6" = some "720"
#guard run "let x = 1 ;; let y = x + 1"          = some "2"
#guard run "assert true ;; 7"                    = some "7"
