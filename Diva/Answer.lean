import Lean.Data.Json

/-!
# Answers of an LLM

Every answer of an LLM to DIVA is in JSON, in a format that the question gives.
DIVA reads the answer and checks it before using it. Any other answer is rejected.
-/

namespace Diva.Answer

open Lean

/-- The JSON value of `answer`. An answer with anything else around the JSON, such as
    text, is an error. -/
def json (answer : String) : Except String Json :=
  (Json.parse answer.trimAscii.toString).mapError fun _ => "the answer is not only JSON"

end Diva.Answer
