import ParseIt
import Diva.Ast

open Std
open ParseIt ParseIt.Char

namespace Diva

abbrev P (α : Type) := Parser (Error.Basic CharIterator) CharIterator Char α

instance : Inhabited (P α) := ⟨throwUnexpected⟩

/-! ### Lexical building blocks -/

/-- A character that may appear at the start of an identifier. -/
def idStart : P Char := tokenFilter (fun c => c.isAlpha || c == '_')

/-- A character that may appear after the first character of an identifier. -/
def idCont : P Char := tokenFilter (fun c =>
  c.isAlphanum || c == '_' || c == '\'')

/-- Skip zero or more whitespace characters. -/
def whitespace : P Unit := dropMany ASCII.whitespace *> pure ()

/-- Run `p`, then skip trailing whitespace. -/
def lexeme (p : P α) : P α := p <* whitespace

/-- A raw identifier `[A-Za-z_][A-Za-z0-9_']*` (keyword or not). -/
def rawIdent : P String := do
  let c ← idStart
  let cs ← takeMany idCont
  return String.ofList (c :: cs.toList)

/-- Reserved words that may not be used as identifiers. -/
def keywords : List String :=
  ["let", "in", "fun", "if", "then", "else", "true", "false", "rec"]

/-- A symbolic token such as `"+"` or `"->"`. -/
def symbol (s : String) : P Unit := lexeme (ParseIt.Char.string s *> pure ())

/-- Read the next operator and return it and its left and right binding
    powers. -/
def opbp: P (BinOp × Nat × Nat) :=
  (symbol "+" *> pure (.add, (1, 2))) <|>
  (symbol "-" *> pure (.sub, (1, 2))) <|>
  (symbol "*" *> pure (.mul, (3, 4)))

/-- A reserved keyword, matched as a whole identifier
    (can't be a prefix of another identifier). -/
def keyword (s : String) : P Unit := lexeme do
  let id ← rawIdent
  if id == s then pure () else throwUnexpected

/-- A non-keyword identifier. -/
def identTok : P String := lexeme do
  let id ← rawIdent
  if keywords.contains id then throwUnexpected else pure id

/-- A natural number literal. -/
def intTok : P Int := lexeme do
  let n ← ASCII.parseNat
  return Int.ofNat n

/-! ### Expression grammar -/

mutual

/-- A full expression, try to parse all constructors one after the other. -/
partial def expr : P Expr :=
  letinxpr <|> funExpr <|> itexpr <|> cmpExpr

/-- `let x = e1 in e2` -/
partial def letinxpr : P Expr := do
  keyword "let"
  let x ← identTok
  symbol "="
  let e1 ← expr
  keyword "in"
  let e2 ← expr
  return .letin x e1 e2

/-- `fun x -> e` -/
partial def funExpr : P Expr := do
  keyword "fun"
  let x ← identTok
  symbol "->"
  let body ← expr
  return .lam x body

/-- `if c then t else e` -/
partial def itexpr : P Expr := do
  keyword "if"
  let c ← expr
  keyword "then"
  let t ← expr
  keyword "else"
  let e ← expr
  return .ite c t e

partial def cmpOp (sym: String) (op: BinOp) (e: Expr) : P Expr := do
  symbol sym
  let r ← pratt 0
  return .binop op e r

/-- Comparisons `=` / `<` (non-associative). -/
partial def cmpExpr : P Expr := do
  let e ← pratt 0
  (cmpOp "=" .eq e) <|>
  (cmpOp "<" .lt e) <|>
  pure e

partial def pratt (lastBp: Nat) : P Expr := do
  let lhs ← appExpr
  prattLoop lhs lastBp

partial def prattLoop (lhs: Expr) (lastBp: Nat) : P Expr := (
    do
      let (op, lbp, rbp) ← opbp
      -- compare with the binding power of the last op (default 0) only bind
      -- to current one if its >= lastBp
      if lbp < lastBp then
        throwUnexpected
      else
        let rhs ← pratt rbp
        prattLoop (.binop op lhs rhs) lastBp
  ) <|> pure lhs

/-- Left-associative application `e e e ...`. -/
partial def appExpr : P Expr := do
  let f ← atom
  appRest f

partial def appRest (f : Expr) : P Expr :=
  (do let a ← atom; appRest (.app f a)) <|>
  pure f

/-- Atoms: parenthesised expr, integer, boolean literal, or variable. -/
partial def atom : P Expr :=
  parenExpr
    <|> (Expr.int <$> intTok)
    <|> boolLit
    <|> (Expr.var <$> identTok)

/-- `( e )` -/
partial def parenExpr : P Expr := do
  symbol "("
  let e ← expr
  symbol ")"
  return e

/-- `true` / `false` -/
partial def boolLit : P Expr :=
  (keyword "true" *> pure (Expr.bool true))
    <|> (keyword "false" *> pure (Expr.bool false))

end

/-- Parse a complete expression, requiring all input to be consumed. -/
def parse (s : String) : Except String Expr :=
  match (whitespace *> expr <* endOfInput).parseString s with
  | .ok e => .ok e
  | .error err => .error s!"Parse error near byte {err.pos.byteIdx}"

end Diva
