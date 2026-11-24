import Diva.Report
import Diva.AbsInt.Fact
import Diva.Parser
import Diva.Answer

/-!
# LLM oracle (untrusted)

The inferred hints (`inferHints`) can be too wide. For example, `f` always returns
`-5`, but the inference finds `[-5, +∞]`, so `10 / f 0` may divide by zero. When the
check fails, an oracle (any LLM) proposes better hints. Works for any domain `A`.

- `prompt` writes the question for the LLM. The question shows the program and the
  places where the program may fail. It also shows the hints that DIVA uses now. If
  the previous answer was rejected, the question says why.
- `parseFacts`: reads the answer, which must be JSON only:
  `{"facts": [{"about": "$f#0", "holds": "-5 <= v && v <= -4"}]}`.
  `about` is a parameter (`x`) or the result of a function `f` (`$f`). `holds` is a
  formula about its value `v` (see `ofFact`).
- `consult`: asks at most `rounds` times, until the program is safe.

The hints are not trusted. The checker checks them like the inferred ones, and
replaces a wrong hint by `top` (any value). So a wrong answer can't make an unsafe
program pass.
-/

namespace Diva.Oracle

open AbsInt Lean

variable {A : Type} [NumDomain A] [ToString A]

/-- One fact `{"about": key, "holds": formula}`, as a hint. `keys` are the hint keys of
    the program. -/
def parseFact (keys : List String) (j : Json) : Except String (String × Flat A) := do
  let k ← (j.getObjValAs? String "about").mapError fun _ => "a fact has no string `about`"
  let h ← (j.getObjValAs? String "holds").mapError fun _ => "a fact has no string `holds`"
  unless keys.contains k do
    throw s!"`{k}` is not a parameter or a function result (`$f`) of the program"
  let t ← (parseTerm h).mapError fun _ => s!"`{h}` is not a formula"
  let a ← (ofFact t).mapError fun msg => s!"`{h}`: {msg}"
  return (k, a)

/-- The hints in an answer `{"facts": [...]}`. Any other answer is an error. `keys`
    are the hint keys of the program. -/
def parseFacts (keys : List String) (answer : String) : Except String (Hints A) := do
  let j ← Answer.json answer
  let fs ← (j.getObjValAs? (Array Json) "facts").mapError fun _ => "the answer has no list `facts`"
  let H ← fs.toList.mapM (parseFact keys)
  if (H.map (·.1)).eraseDups.length != H.length then
    throw "two facts are about the same name"
  return H

/-- The hints `H`, one per line, as `diva hints` prints them. -/
def render (H : Hints A) : String :=
  "\n".intercalate (H.map fun (x, a) => s!"  {x} : {a}")

/-- The program `e`, whose free variables `σ` describes, is safe with the hints
    `fixed`, and the ones inferred. -/
def verifies (σ : AEnv A) (e : Expr) (fixed : Hints A) : Bool :=
  !mayFail (inferHints σ e fixed) σ e

/-- `s` with two spaces at the start of each line. -/
private def indent (s : String) : String :=
  "\n".intercalate ((s.trimAsciiEnd.toString.splitOn "\n").map ("  " ++ ·))

/-- The question to the oracle about the program `e`. `fixed` are the hints of the
    previous answer, and `rejected` says why it was rejected (`none` in the first
    round). With `src`, the question also shows the source, and the places where the
    program may fail have their positions in it. -/
def prompt (σ : AEnv A) (e : Expr) (fixed : Hints A) (rejected : Option String)
    (src : Option Source := none) : String :=
  let rejected := match rejected with
    | none => ""
    | some why => s!"\nYour previous answer was rejected: {why}\n"
  let source := match src with
    | none => ""
    | some s => s!"The source, in `{s.file}`:\n\n{indent s.text}\n\n"
  let place (sp : Span) : String := match src with
    | none => ""
    | some s => sp.format s.text s.file
  let loc := (src.map (·.loc)).getD default
  let positions := if src.isSome then " (`file:line:col-col`, lines from 1, columns from 0)" else ""
  s!"DIVA, a verifier for a small ML-like language, can't prove that this program never
fails (division by zero, failed `assert`, type error).

{source}The program as DIVA reads it (each parameter and each recursive function has a
unique name):

  {ppExpr e}

Where it may fail{positions}:

{"\n".intercalate ((Report.report σ e fixed loc place).map ("  " ++ ·))}

What DIVA knows about the values (`x` is the parameter `x`, `$f` is the result of the
function `f`):

{render (inferHints σ e fixed)}
{rejected}
Give facts about these values that rule out these failures. Each fact is checked: a
wrong one is rejected. If the program can really fail, give no fact.

Answer with JSON only, in this format:

  \{\"facts\": [\{\"about\": \"x#3\", \"holds\": \"0 <= v && v < 10\"}, \{\"about\": \"$g#2\", \"holds\": \"v = 7\"}]}

`about` is one of the names above. `holds` is a formula about the value, named `v`:
comparisons of `v` with an integer (`=`, `<>`, `<`, `<=`, `>`, `>=`), joined by `&&`."

/-- One round: the hints proposed by the oracle, why its answer can't be read (if it
    can't), and whether the program is safe with the hints. -/
structure Round (A : Type) where
  hints : Hints A
  error : Option String := none
  accepted : Bool

/-- Ask `oracle` for hints, at most `rounds` times, until the program `e` is safe with
    them. `σ` describes the free variables of `e`. `src` is the source of `e`, for the
    positions in the questions. Returns the rounds. If `e` is safe
    without hints, the oracle isn't asked. -/
def consult [Monad m] (oracle : String → m String) (σ : AEnv A) (e : Expr)
    (rounds : Nat := 3) (src : Option Source := none) : m (List (Round A)) :=
  if verifies σ e [] then return [] else go rounds [] none
where
  go : Nat → Hints A → Option String → m (List (Round A))
    | 0, _, _ => return []
    | k + 1, fixed, rejected => do
      let answer ← oracle (prompt σ e fixed rejected src)
      match parseFacts (hintKeys e).eraseDups answer with
      | .error msg =>
        return { hints := [], error := some msg, accepted := false } ::
          (← go k [] (some s!"it isn't in the format: {msg}"))
      | .ok hints =>
        if verifies σ e hints then return [{ hints, accepted := true }]
        if hints.isEmpty then return [{ hints, accepted := false }]
        return { hints, accepted := false } ::
          (← go k hints (some s!"the checker rejected these facts:\n{render hints}"))

end Diva.Oracle
