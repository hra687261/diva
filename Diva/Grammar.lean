/-!
# The grammar in the questions to the LLM

`grammar` is the text of `doc/grammar.md`: the grammar of the language and of the
contracts, with the commands that support each rule. The questions to the LLM include
it. `include_str` reads the file when this module is built, so `diva` doesn't need
the file when it runs.

Lake doesn't rebuild this module when only `doc/grammar.md` changes.
-/

namespace Diva

/-- The text of `doc/grammar.md`. -/
def grammar : String := include_str "../doc/grammar.md"

end Diva
