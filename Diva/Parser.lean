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
  ["let", "in", "fun", "if", "then", "else", "true", "false", "rec",
   "match", "with", "mod", "not", "assert", "_"]

/-- A symbolic token such as `"+"` or `"->"`. -/
def symbol (s : String) : P Unit := lexeme (ParseIt.Char.string s *> pure ())

/-- A reserved keyword, matched as a whole identifier
    (can't be a prefix of another identifier). -/
def keyword (s : String) : P Unit := lexeme do
  let id ← rawIdent
  if id == s then pure () else throwUnexpected

/-- Read the next operator and return its node builder and its left and right
    binding powers. -/
def opbp: P ((Expr → Expr → Expr) × Nat × Nat) :=
  (symbol "::"   *> pure (.cons, (0, 0)))       <|>
  (symbol "+"    *> pure (.binop .add, (1, 2))) <|>
  (symbol "-"    *> pure (.binop .sub, (1, 2))) <|>
  (symbol "*"    *> pure (.binop .mul, (3, 4))) <|>
  (symbol "/"    *> pure (.binop .div, (3, 4))) <|>
  (keyword "mod" *> pure (.binop .mod, (3, 4)))

/-- A non-keyword identifier. -/
def identTok : P String := lexeme do
  let id ← rawIdent
  if keywords.contains id then throwUnexpected else pure id

/-- bound variable names: an identifier or the wildcard `_`. -/
def binderTok : P String := identTok <|> (keyword "_" *> pure "_")

/-- A natural number literal. -/
def intTok : P Int := lexeme do
  let n ← ASCII.parseNat
  return Int.ofNat n

/-- `fun x y -> e` is `fun x -> fun y -> e`. -/
def lams (xs : List String) (body : Expr) : Expr := xs.foldr .lam body

/-! ### Expression grammar -/

mutual

/-- `e1; e2` is `let _ = e1 in e2`. -/
partial def seqExpr : P Expr := do
  let e ← expr
  (do symbol ";"; let r ← seqExpr; return .letin "_" e r) <|> pure e

/-- A full expression, try to parse all constructors one after the other. -/
partial def expr : P Expr :=
  letinxpr <|> funExpr <|> itexpr <|> matchExpr <|> orExpr

/-- `let [rec] f x y = e`, shared by `let … in` and top-level declarations. -/
partial def binding : P (String × (Expr → Expr)) := do
  keyword "let"
  let isRec := (← option? (keyword "rec")).isSome
  let f ← binderTok
  let ps := (← takeMany binderTok).toList
  symbol "="
  let rhs ← seqExpr
  match isRec, ps, rhs with
  | false, _, _ => return (f, .letin f (lams ps rhs))
  | true, x :: ps, _ => return (f, .letrec f x (lams ps rhs))
  | true, [], .lam x rhs' => return (f, .letrec f x rhs')
  | true, [], _ => throwUnexpected -- `let rec` must define a function

/-- `let x = e1 in e2` -/
partial def letinxpr : P Expr := do
  let (_, k) ← binding
  keyword "in"
  -- fun e2 -> (let [_ = e1]* in e2)
  let e2 ← seqExpr
  return k e2

/-- `fun x y -> e` -/
partial def funExpr : P Expr := do
  keyword "fun"
  let xs ← takeMany1 binderTok
  symbol "->"
  let body ← seqExpr
  return lams xs.toList body

/-- `if c then t else e` -/
partial def itexpr : P Expr := do
  keyword "if"
  let c ← expr
  keyword "then"
  let t ← expr
  keyword "else"
  let e ← expr
  return .ite c t e

/-- `match s with [] -> n | x :: xs -> c` -/
partial def matchExpr : P Expr := do
  keyword "match"
  let s ← seqExpr
  keyword "with"
  symbol "["; symbol "]"; symbol "->"
  let n ← seqExpr
  symbol "|"
  let x ← binderTok
  symbol "::"
  let xs ← binderTok
  symbol "->"
  let c ← seqExpr
  return .matchList s n x xs c

/-- `a || b` is `if a then true else b`. -/
partial def orExpr : P Expr := do
  let a ← andExpr
  (do symbol "||"; let b ← orExpr; return .ite a (.bool true) b) <|> pure a

/-- `a && b` is `if a then b else false`. -/
partial def andExpr : P Expr := do
  let a ← cmpExpr
  (do symbol "&&"; let b ← andExpr; return .ite a b (.bool false)) <|> pure a

partial def cmpOp (sym: String) (op: BinOp) (e: Expr) : P Expr := do
  symbol sym
  let r ← pratt 0
  return .binop op e r

/-- Comparisons (non-associative). -/
partial def cmpExpr : P Expr := do
  let e ← pratt 0
  (cmpOp "=" .eq e) <|>
  (cmpOp "<>" .ne e) <|>
  (cmpOp "<=" .le e) <|>
  (cmpOp "<" .lt e) <|>
  (cmpOp ">=" .ge e) <|>
  (cmpOp ">" .gt e) <|>
  pure e

partial def pratt (lastBp: Nat) : P Expr := do
  let lhs ← unary
  prattLoop lhs lastBp

partial def prattLoop (lhs: Expr) (lastBp: Nat) : P Expr := (
    do
      let (builder, lbp, rbp) ← opbp
      -- compare with the binding power of the last op (default 0) only bind
      -- to current one if its >= lastBp
      if lbp < lastBp then
        throwUnexpected
      else
        let rhs ← pratt rbp
        prattLoop (builder lhs rhs) lastBp
  ) <|> pure lhs

/-- `-e` (`0 - e`), `not e`, `assert e`. -/
partial def unary : P Expr :=
  (do
    symbol "-"
    let e ← unary
    return .binop .sub (.int 0) e) <|>
  (do
    keyword "not"
    let e ← unary
    return .ite e (.bool false) (.bool true)) <|>
  (do
    keyword "assert"
    let e ← unary
    return .assert e) <|>
  appExpr

/-- Left-associative application `e e e ...`. -/
partial def appExpr : P Expr := do
  let f ← atom
  appRest f

partial def appRest (f : Expr) : P Expr :=
  (do let a ← atom; appRest (.app f a)) <|>
  pure f

/-- Atoms: parenthesised expr, `()`, `[]`, integer, boolean literal, or variable. -/
partial def atom : P Expr :=
  parenExpr
    <|> (symbol "(" *> symbol ")" *> pure Expr.unit)
    <|> (symbol "[" *> symbol "]" *> pure Expr.nil)
    <|> (Expr.int <$> intTok)
    <|> boolLit
    <|> (Expr.var <$> identTok)

/-- `( e )` -/
partial def parenExpr : P Expr := do
  symbol "("
  let e ← seqExpr
  symbol ")"
  return e

/-- `true` / `false` -/
partial def boolLit : P Expr :=
  (keyword "true" *> pure (Expr.bool true))
    <|> (keyword "false" *> pure (Expr.bool false))

end

/-- A top-level item: a declaration `let f x = e` (without `in`), or an
    expression. -/
inductive Item where
  | decl : String → (Expr → Expr) → Item
  | expr : Expr → Item

def declItem : P Item := do
  let (f, k) ← binding
  return .decl f k

def item : P Item :=
  (Item.expr <$> letinxpr) <|>
  declItem <|>
  (Item.expr <$> seqExpr)

/-- A program is nested `let`s ending in the value of its last item. -/
def Item.toExpr : List Item → Expr
  | [] => .unit
  | [.expr e] => e
  | .expr e :: r => .letin "_" e (Item.toExpr r)
  | [.decl f k] => k (.var f)
  | .decl _ k :: r => k (Item.toExpr r)

/-- A program: top-level items.
    As in OCaml, `;;` is optional between declarations but required before an
    expression that isn't first. -/
def program : P Expr := do
  let _ ← dropMany (symbol ";;")
  let first ← option? item
  let rest ← takeMany (declItem <|> (takeMany1 (symbol ";;") *> item))
  let _ ← dropMany (symbol ";;")
  return Item.toExpr (first.toList ++ rest.toList)

/-- Parse a complete program. -/
def parse (s : String) : Except String Expr :=
  match (whitespace *> program <* endOfInput).parseString s with
  | .ok e => .ok e
  | .error err => .error s!"Parse error near byte {err.pos.byteIdx}"

end Diva
