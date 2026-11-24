import Diva.Commands
import Diva.AbsInt.ItvDomain

open Diva Commands

-- `run`: the value, or a runtime error with exit code 1
#guard run "let f x = x * 2 in f 21" == { out := ["42"] }
#guard run "1 / 0" == { err := ["runtime error: division by zero"], code := 1 }
#guard run "let rec f x = f x in f 0" == { err := ["out of fuel"], code := 1 }
#guard run "1 +" == { err := ["parse error: Parse error at 1:2"], code := 1 }
#guard run "let x = 1\n  in x +" == { err := ["parse error: Parse error at 2:7"], code := 1 }

-- `check`: exit code 1 if the program may fail
#guard check "let f y = 10 / y in f 3" == { out := ["no runtime error is possible"] }
#guard check "let f y = 10 / y in f 0" == {
  out := ["`(10 / y)`: possible division by zero (divisor: 0)",
          "`(f 0)`: the function called may fail"],
  code := 1 }
-- with a file name, each message starts with its position: `file:line:col-col`, with
-- lines from 1 and columns from 0, as in Lean
#guard check (file := some "f.ml") "let f y =\n  10 / y\n;; f 0" == {
  out := ["f.ml:2:2-8: `(10 / y)`: possible division by zero (divisor: 0)",
          "f.ml:3:3-6: `(f 0)`: the function called may fail"],
  code := 1 }
-- a comment after an expression isn't in its span
#guard check (file := some "f.ml") "let f y = 10 / y (* y = 0 *)\n;; f 0" == {
  out := ["f.ml:1:10-16: `(10 / y)`: possible division by zero (divisor: 0)",
          "f.ml:2:3-6: `(f 0)`: the function called may fail"],
  code := 1 }

-- `opt`: the optimised program, without the `#n` suffixes of names
#guard opt "let x = 2 in if x < 3 then x * 1 else 0" == { out := ["2"] }
#guard opt "fun y -> let x = 2 in if x < 3 then y + 1 else y" ==
  { out := ["(fun y -> (let x = 2 in (y + 1)))"] }

-- `hints`: one line per hint, names with their `#n` suffix, `$f` for results
#guard hints "let f y = 10 / y in f 3 + f 7" == { out := ["y#0 : [3, 7]"] }
#guard hints "let rec g n = if n <= 0 then 0 else g (n - 1) in g 5" ==
  { out := ["n#1 : [0, 5]", "$g#0 : 0"] }

-- `cert`: a Lean file stating that the program can't fail, or nothing if it may fail
#guard ((cert "10 / 2").out.head!.splitOn "\n").contains "  (.binop .div (.int 10) (.int 2))"
#guard cert "10 / 0" == {
  err := ["the program may fail, so there is no certificate (see `diva check`)"], code := 1 }

-- programs and hints as Lean terms
#guard Cert.expr (.letin "x" (.int (-5)) (.var "x")) = "(.letin \"x\" (.int (-5)) (.var \"x\"))"
#guard Cert.hints [("y#0", AbsInt.Flat.ofInt (.range (.fin 3) .posInf))] =
  "[\n  (\"y#0\", { int := (.range (.fin 3) .posInf), tt := false, ff := false, unit := false, \
list := false, fn := false, loc := false, exn := false })]"

-- `prove`: a function with a contract must come before the values and the expressions
#guard (prove "let y = 3\nlet f x = x + 1\n(*@ r = f x ensures r > x *)").err ==
  ["`f` has a contract, but `y`, defined before it, isn't a function: not supported yet"]
#guard (prove ";; 1\nlet f x = x + 1\n(*@ r = f x ensures r > x *)").err ==
  ["`f` has a contract, but an expression `;; ...` comes before it: not supported yet"]

-- `prove --infer`: a function without a contract gets the contract of its hints
#guard (SpecOfHints.inferContracts ((parseItems
  "let rec count n = if n <= 0 then 0 else 1 + count (n - 1)\n;; count 5").toOption.getD [])).2 ==
  ["count"]
#guard (SpecOfHints.inferContracts ((parseItems "let f x = x\n;; f true").toOption.getD [])).2 ==
  []

-- `requires` is checked when the function is called: a call that breaks it fails. The
-- header `r = f y` names the parameter `y`, which is `x` in the code.
#guard run "let f x = x\n(*@ requires x >= 0 *)\n;; f (0 - 1)" ==
  { err := ["runtime error: assertion failed"], code := 1 }
#guard run "let f x = x\n(*@ r = f y\n    requires y >= 0 *)\n;; f (0 - 1)" ==
  { err := ["runtime error: assertion failed"], code := 1 }
#guard run "let f x = x\n(*@ requires x >= 0 *)\n;; f 2" == { out := ["2"] }
