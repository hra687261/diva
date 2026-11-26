import Diva.Commands

open Diva Commands

/-! The overflow checks for an integer type (`Overflow`). -/

-- the bounds of OCaml's integer types
#guard IntType.int63.min == -4611686018427387904 && IntType.int63.max == 4611686018427387903
#guard IntType.int32.min == -2147483648 && IntType.int32.max == 2147483647
#guard IntType.int64.max == 9223372036854775807

/-- The program `s` as DIVA reads it, with integers of `bits` bits. -/
def checked (bits : Nat) (s : String) : String :=
  match parse s (some ⟨bits⟩) with
  | .ok e => Report.clean (toString e)
  | .error m => m

-- `+`, `-`, `*` and `/` are checked, `mod` and the comparisons aren't
#guard checked 4 "1 + 2" ==
  "(let %r = (1 + 2) in (let _ = (assert (if (-8 <= %r) then (%r <= 7) else false)) in %r))"
#guard checked 4 "7 mod 2 < 1" == "((7 mod 2) < 1)"
-- a contract keeps integers without bound
#guard checked 4 "let f x = x\n(*@ requires x + 1 > 0 *)" ==
  "(let f = (fun x -> (let _ = (assert ((x + 1) > 0)) in x)) in f)"

-- `7 + 1` doesn't fit in 4 bits: `run` fails, and `check` says why
#guard run "7 + 1" (intTy := some ⟨4⟩) == { err := ["runtime error: assertion failed"], code := 1 }
#guard (check "7 + 1" (intTy := some ⟨4⟩)).out == ["`(7 + 1)`: may overflow 4-bit integers (result: 8)"]
#guard (check "7 + 1" (intTy := some ⟨5⟩)).out == ["no runtime error is possible"]
-- `min / -1` is the only `/` that overflows
#guard (check "let x = 0 - 8 in let y = 0 - 1 in x / y" (intTy := some ⟨4⟩)).out ==
  ["`(x / y)`: may overflow 4-bit integers (result: 8)"]
-- once the analysis proves the checks, `opt` erases them
#guard (opt "let x = 3 in x * x" (intTy := some .int63)).out == ["9"]
