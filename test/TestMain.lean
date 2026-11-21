import ParserTest
import InterpTest
import AbsIntItv
import AbsIntTest
import ReportTest
import OptTest
import CommandsTest
import DeductiveTest

/-! The test driver of `lake test`. Building it builds the test modules above, which
checks their `#guard`s. Running it runs the end-to-end tests of `test/cli.sh`. -/

def main : IO UInt32 := do
  let child ← IO.Process.spawn { cmd := "test/cli.sh" }
  child.wait
