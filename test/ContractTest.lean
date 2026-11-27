import Diva.Parser
import Diva.AbsInt.ItvDomain
import Diva.AbsInt.Fact
import Diva.Prove

open Diva Diva.AbsInt

/-! Contracts with booleans and lists: the terms, the kind of each name, the facts, and
the Lean terms that `diva prove` writeMsgs. -/

-- the terms: `true`, `false`, `not`, `||`, and `length l` (also `List.length l`)
#guard (parseTerm "not b || length l >= 2").toOption ==
  some (.or (.not (.var "b")) (.binop .ge (.length (.var "l")) (.int 2)))
#guard (parseTerm "r = (List.length l = 0) && true").toOption ==
  some (.and (.binop .eq (.var "r") (.binop .eq (.length (.var "l")) (.int 0))) (.bool true))

/-- The kind of `x` in the clauses `s`. -/
private def kind (s : String) (x : String) : Option Kind :=
  (parseTerm s).toOption.map (kindOf [·] x)

-- the kind of a name comes from how the contract uses it
#guard kind "b || x = y" "b" == some .bool
#guard kind "b || x = y" "x" == some .int
#guard kind "r = not b" "r" == some .bool
#guard kind "r = (length l = 0)" "l" == some .list
#guard kind "r = (length l = 0)" "r" == some .bool
#guard kind "x = y" "x" == some .int   -- nothing says otherwise: an integer

/-- The values of `v` that the fact `s` describes, printed. -/
private def fact (s : String) : String :=
  match (parseTerm s).toOption.map (ofFact (A := Itv)) with
  | some (.ok a) => toString a
  | some (.error e) => e
  | none => "not a term"

-- facts about booleans and lists, for the hints of an LLM
#guard fact "v" == "true"
#guard fact "not v" == "false"
#guard fact "v = false" == "false"
#guard fact "length v > 0" == "non-empty list"
#guard fact "length v >= 0" == "list"

/-- The Lean proposition that `diva prove` writes for the term `s`, where `b` is a
    boolean, `l` a list, and the other names integers. -/
private def lean (s : String) : String :=
  let kinds (x : String) : Kind := if x == "b" then .bool else if x == "l" then .list else .int
  match parseTerm s with
  | .ok t => Prove.propTerm kinds t
  | .error e => e

#guard lean "b || x = y" == "((b = true) ∨ (x = y))"
#guard lean "r = not b" == "((r = true) ↔ (¬ (b = true)))"
#guard lean "length l >= 2" == "((Diva.Value.length l) ≥ 2)"
