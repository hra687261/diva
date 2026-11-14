import Diva.Parser
import Diva.Interp

/-- Parse and run `s`, and return its outcome, a value, an error, or none if out
    of fuel -/
private def run (s : String) : Option String := do
  let e ← (Diva.parse s).toOption
  let (r, _) ← Diva.eval 1000 [] [] e
  return toString r

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

-- arrays
#guard run "let a = Array.make 3 0 in a.(1) <- 5; a.(1) + a.(0)" = some "5"
#guard run "let a = Array.make 1 0 in a.(0) <- a.(0) + 1; a.(0) <- a.(0) + 1; a.(0)" = some "2"
#guard run "Array.length (Array.make 4 true)"   = some "4"

-- arrays are shared
#guard run "let a = Array.make 1 0 in let b = a in b.(0) <- 7; a.(0)" = some "7"
#guard run "let a = Array.make 2 0 in a.(2)"    = some "error: index out of bounds"
#guard run "let a = Array.make 2 0 in a.(-1) <- 1" = some "error: index out of bounds"
#guard run "Array.make (-1) 0"                  = some "error: index out of bounds"
#guard run "1.(0)"                              = some "error: type error"

-- refs
#guard run "let r = ref 1 in r := !r + 41; !r"   = some "42"
#guard run "let r = ref 0 in incr r; incr r; decr r; !r" = some "1"
#guard run "let r = ref 0 in let rec loop n = if n = 0 then () else (r := !r + n; loop (n - 1)) in loop 4; !r" = some "10"

-- refs and arrays are different kinds of values
#guard run "let r = ref 0 in r.(0)"             = some "error: type error"
#guard run "let a = Array.make 1 0 in !a"       = some "error: type error"
#guard run "let a = Array.make 1 0 in a := 1"   = some "error: type error"
#guard run "ref 0"                              = some "<ref 0>"

-- loops
#guard run "let s = ref 0 in for i = 1 to 4 do s := !s + i done; !s" = some "10"
#guard run "let s = ref 0 in for i = 1 to 0 do s := !s + 1 done; !s" = some "0"
#guard run "let n = ref 5 in let c = ref 0 in while !n > 0 do decr n; incr c done; !c" = some "5"

-- nested loops: the inner `%for` does not capture the outer one
#guard run "let s = ref 0 in for i = 1 to 3 do for j = 1 to 2 do incr s done done; !s" = some "6"
#guard run "let a = Array.make 3 0 in for i = 0 to 3 do a.(i) <- i done" = some "error: index out of bounds"

-- exceptions are values; raising one stops the program
#guard run "E"                                  = some "E"
#guard run "E (1 + 2)"                          = some "(E 3)"
#guard run "raise E"                            = some "error: uncaught exception E"
#guard run "raise (E 1); 2"                     = some "error: uncaught exception (E 1)"
#guard run "let r = ref 0 in for i = 1 to 5 do (if i = 3 then raise Stop); incr r done" =
  some "error: uncaught exception Stop"
#guard run "raise 1"                            = some "error: type error"

-- catching exceptions: handlers are tried in order, unmatched ones are re-raised
#guard run "try raise E with E -> 1"            = some "1"
#guard run "try raise (E 5) with E x -> x + 1"  = some "6"
#guard run "try 3 with E -> 1"                  = some "3"
#guard run "try raise (F 1) with E x -> x | F y -> y * 10" = some "10"
#guard run "try raise G with E -> 1 | F -> 2"   = some "error: uncaught exception G"
#guard run "try raise (E 2) with k -> k"        = some "(E 2)"
#guard run "try (try raise E with F -> 1) with E -> 2" = some "2"

-- runtime errors are not exceptions: `try` does not catch them
#guard run "try 1 / 0 with _ -> 0"              = some "error: division by zero"
#guard run "try assert false with _ -> 0"       = some "error: assertion failed"

-- the store is kept when an exception is caught: exiting a loop early
#guard run "let r = ref 0 in try for i = 1 to 10 do (if i = 4 then raise Stop); incr r done with Stop -> !r" =
  some "3"
