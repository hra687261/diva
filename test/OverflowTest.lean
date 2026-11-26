import Diva.Commands

open Diva Commands

/-! The overflow checks for an integer type (`Overflow`). -/

-- the bounds of the integer types
#guard IntType.int63.min == -4611686018427387904 && IntType.int63.max == 4611686018427387903
#guard IntType.int32.min == -2147483648 && IntType.int32.max == 2147483647
#guard IntType.int64.max == 9223372036854775807

/-- DIVA's parser, with integers of `bits` bits. -/
def bitsReader (bits : Nat) : Reader := parseItemsLoc.withIntTy (some ⟨bits⟩)

/-- The program `s` as DIVA reads it, with integers of `bits` bits. -/
def checked (bits : Nat) (s : String) : String :=
  match (bitsReader bits).expr s with
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
#guard run "7 + 1" (read := bitsReader 4) == { err := ["runtime error: assertion failed"], code := 1 }
#guard (check "7 + 1" (read := bitsReader 4)).out == ["`7 + 1`: may overflow 4-bit integers (result: 8)"]
#guard (check "7 + 1" (read := bitsReader 5)).out == ["no runtime error is possible"]
-- `min / -1` is the only `/` that overflows
#guard (check "let x = 0 - 8 in let y = 0 - 1 in x / y" (read := bitsReader 4)).out ==
  ["`x / y`: may overflow 4-bit integers (result: 8)"]
-- once the analysis proves the checks, `opt` erases them
#guard (opt "let x = 3 in x * x" (read := bitsReader 63)).out == ["9"]

-- an integer literal that doesn't fit is an error, with its position
#guard check "1 +\n  4611686018427387904" (read := bitsReader 63) ==
  { err := ["2:2: the integer 4611686018427387904 doesn't fit in 63-bit integers"], code := 1 }
#guard (check "-9" (read := bitsReader 4)).err ==
  ["1:1: the integer 9 doesn't fit in 4-bit integers"]
-- `-n` may be the smallest integer: `-8` fits in 4 bits
#guard (check "-8" (read := bitsReader 4)).out == ["no runtime error is possible"]
