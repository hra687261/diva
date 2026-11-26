import Diva.Ast

/-!
# Source locations (untrusted)

`Expr` has no positions, so the proofs don't see them. The parser also gives a tree
of positions (`Loc`) with the same shape, as Lean's info trees do for its terms.

A `Loc` node has a span, and the `Loc`s of the sub-expressions in constructor order:
`ite c t e` has `c`, `t`, `e`. A missing child gets its parent's span (`Loc.kid`).
-/

namespace Diva

/-- A part of the source: the bytes from `start` to `stop`. -/
structure Span where
  start : Nat
  stop : Nat
  deriving Inhabited, Repr, BEq

/-- The positions of an expression: its span, and the positions of its
    sub-expressions. -/
inductive Loc where
  | node : Span → List Loc → Loc
  deriving Inhabited

/-- The span of the expression. -/
def Loc.span : Loc → Span
  | .node s _ => s

/-- The positions of the `i`-th sub-expression. If the tree has no child `i`, the
    positions of the expression itself. -/
def Loc.kid (l : Loc) (i : Nat) : Loc :=
  match l with
  | .node _ ks => ks.getD i l

/-- The positions of an expression without sub-expressions, or of code that the
    parser adds. -/
def Loc.leaf (s : Span) : Loc := .node s []

/-- An expression with its positions. -/
structure LExpr where
  expr : Expr
  loc : Loc
  deriving Inhabited

/-- A user-provided program: the name of its file, its text, and the positions of
    its expression. -/
structure Source where
  file : String
  text : String
  loc : Loc

/-- The line (from 1) and the column (from 0) of the byte `off` of `src`. -/
def lineCol (src : String) (off : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 0
  let mut i := 0
  for c in src.toList do
    if i ≥ off then break
    if c == '\n' then
      line := line + 1
      col := 0
    else
      col := col + 1
    i := i + c.utf8Size
  return (line, col)

/-- The end of the last character of `src` between the bytes `start` and `stop` that
    isn't a space or in a comment `(* ... *)`. A span ends after the spaces and comments
    that the parser skips after each token. -/
def trimEnd (src : String) (start stop : Nat) : Nat := Id.run do
  let mut last := start
  -- `last` before the latest `(`, in case the `(` starts a comment
  let mut beforeParen := start
  let mut i := 0
  let mut inComment := false
  let mut prev := ' '
  for c in src.toList do
    if i ≥ stop then break
    i := i + c.utf8Size
    if i > start then
      if inComment then
        if prev == '*' && c == ')' then
          inComment := false
          prev := ' '
          continue
      else if prev == '(' && c == '*' then
        inComment := true
        last := beforeParen
      else if !c.isWhitespace then
        if c == '(' then beforeParen := last
        last := i
    prev := c
  return max start last

/-- The text of `src` in the span `s`, on one line: each run of spaces and newlines
    becomes one space. `""` if `s` isn't a part of `src`. -/
def Span.text (src : String) (s : Span) : String :=
  let stop := trimEnd src s.start s.stop
  let t := (String.fromUTF8? (src.toUTF8.extract s.start stop)).getD ""
  -- `space`: a space comes before the next character
  let (out, _) := t.toList.foldl (init := ("", false)) fun (acc, space) c =>
    if c.isWhitespace then (acc, true)
    else ((if space && !acc.isEmpty then acc.push ' ' else acc).push c, false)
  out

/-- `s` as `file:line:col-col`, or `file:line:col-line:col` if it spans several lines,
    as in Lean's messages: lines from 1, columns from 0. -/
def Span.format (src file : String) (s : Span) : String :=
  let (l1, c1) := lineCol src s.start
  let (l2, c2) := lineCol src (trimEnd src s.start s.stop)
  if l1 == l2 then s!"{file}:{l1}:{c1}-{c2}" else s!"{file}:{l1}:{c1}-{l2}:{c2}"

end Diva
