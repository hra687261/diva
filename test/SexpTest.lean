import Diva.Commands
import Diva.Sexp

open Diva Commands

/-! The S-expressions of the OCaml front end, written by hand. -/

/-- The OCaml file. -/
private def src := "let f x = 10 / x\nlet _ = f 0"

/-- Its program, as the front end prints it. The numbers are byte offsets in `src`:
    `10 / x` is the bytes 10 to 16. -/
private def sexp := "(program
  (let \"f\" (lam 6 16 \"x\" (binop 10 16 div (int 10 12 10) (var 15 16 \"x\"))))
  (expr (app 25 28 (var 25 26 \"f\") (int 27 28 0))))"

/-- The reader of the front end, for the program `s`. -/
private def read (s : String) : Reader := fun _ => Sexp.items s

-- the commands work on the program read, with the positions in `src`
#guard run src (read := read sexp) ==
  { err := ["runtime error: division by zero"], code := 1 }
#guard check src (file := some "f.ml") (read := read sexp) ==
  { out := ["f.ml:1:10-16: `(10 / x)`: possible division by zero (divisor: 0)",
            "f.ml:2:8-11: `(f 0)`: the function called may fail"],
    code := 1 }

-- a contract is the text of its comment: `requires` is checked, and erased by `opt`
-- because the program never fails
#guard opt "" (read := read "(program
  (let \"f\" (lam 0 1 \"x\" (var 0 1 \"x\")) \"(*@ requires x >= 0 *)\")
  (expr (app 0 1 (var 0 1 \"f\") (int 0 1 0))))") ==
  { out := ["(let f = (fun x -> x) in (f 0))"] }

/-- The error of `Sexp.items` on `s`, or `ok`. -/
private def err (s : String) : String :=
  match Sexp.items s with
  | .ok _ => "ok"
  | .error m => m

#guard err "(program (let f (int 0 1 2)))" == "`f` is not a name in quotes"
#guard err "(program (expr (int 0 1 2))" == "a list has no `)`"
#guard err "(program (expr (foo 0 1)))" == "`(foo 0 1)` is not an expression"
-- the position of an error in a contract is in its text: the front end puts spaces and
-- newlines before the comment, so that the position is the one in the file
#guard err "(program (let \"f\" (int 0 1 2) \"(*@ requires *)\"))" == "1:4: parse error"
