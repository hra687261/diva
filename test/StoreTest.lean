import Diva.Commands

open Diva Commands

/-! The analysis of arrays and refs (`aevalExt`, `mayFailExt`), in `diva check`. It isn't
proved yet: `check` says so when only this analysis shows that a program can't fail. -/

-- a ref: its contents are the hint `!0`, which the inference finds
#guard (check "let r = ref 0 in r := !r + 1; !r").out == [Report.unprovedSafe]
#guard (check "!3").out == ["`!3`: may not be a ref (3)"]

-- an array: its length is the hint `!0.length`, and each index is checked
#guard (check "let a = Array.make 3 0 in a.(3)").out ==
  ["`a.(3)`: the index (3) may be out of bounds (length: 3)"]
#guard (check "let a = Array.make 10 0 in for i = 0 to 9 do a.(i) <- i done; a.(5)").out ==
  [Report.unprovedSafe]
#guard (hints "let a = Array.make 10 0 in for i = 0 to 9 do a.(i) <- i done; a.(5)").out ==
  ["!0 : [0, 9]", "!0.length : 10", "i#1 : [0, 10]", "$%for#0 : ()"]
#guard (check "Array.make (0 - 1) 0").out == ["`Array.make (0 - 1) 0`: the length may be negative (-1)"]

-- what is read is what was written: here `true` too
#guard (check "let a = Array.make 2 0 in a.(0) <- true; a.(1) + 1").out ==
  ["`a.(1) + 1`: the operands may not be integers (0 | true and 1)"]

-- a parameter knows the sites of its arrays: here two sites, of lengths 3 and 1
#guard (check "let f a = a.(0) in f (Array.make 3 1) + f (Array.make 1 2)").out ==
  [Report.unprovedSafe]
#guard (check "let f a i = a.(i) in f (Array.make 3 1) 3").out ==
  ["`a.(i)`: the index (3) may be out of bounds (length: 3) (in the call `f (Array.make 3 1) 3`)"]

-- the exit code follows the analysis of the store, but `cert` needs the proved checker
#guard (check "let r = ref 0 in !r").code == 0
#guard cert "let r = ref 0 in !r" == { err := ["the analysis of arrays, refs, \
  exceptions and the elements of lists isn't proved yet, so there is no certificate (see `diva check`)"], code := 1 }
