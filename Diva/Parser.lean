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
   "match", "with", "mod", "not", "assert", "_",
   "for", "to", "do", "done", "while", "raise", "try"]

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

/-- A variable: a non-keyword identifier that is not capitalised. -/
def identTok : P String := lexeme do
  let id ← rawIdent
  if keywords.contains id || id.front.isUpper then throwUnexpected else pure id

/-- An exception constructor: a capitalised identifier, such as `Not_found`. -/
def ctorTok : P String := lexeme do
  let id ← rawIdent
  if id.front.isUpper then pure id else throwUnexpected

/-- bound variable names: an identifier or the wildcard `_`. -/
def binderTok : P String := identTok <|> (keyword "_" *> pure "_")

/-- A natural number literal. -/
def intTok : P Int := lexeme do
  let n ← ASCII.parseNat
  return Int.ofNat n

/-- `fun x y -> e` is `fun x -> fun y -> e`. -/
def lams (xs : List String) (body : Expr) : Expr := xs.foldr .lam body

/-- The pattern of a `try` handler: `E x` / `E` (an exception tag), or `k` / `_`
    (any exception). -/
inductive Handler where
  | tag : String → String → Handler
  | any : String → Handler

/-- `try e with p1 -> h1 | … | pn -> hn` catches the exception as `%exn` (a name
    users cannot write), then tries the handlers in order.
    An exception no handler matches is raised again. -/
def tryWith (e : Expr) (arms : List (Handler × Expr)) : Expr :=
  .tryw e "%exn" (go arms)
where
  go : List (Handler × Expr) → Expr
    | [] => .raise (.var "%exn")
    | (.tag c x, h) :: rest => .exnCase (.var "%exn") c x h (go rest)
    | (.any k, h) :: _ => .letin k (.var "%exn") h

/-! ### Expression grammar -/

mutual

/-- `e1; e2` is `let _ = e1 in e2`. -/
partial def seqExpr : P Expr := do
  let e ← expr
  (do symbol ";"; let r ← seqExpr; return .letin "_" e r) <|> pure e

/-- A full expression, try to parse all constructors one after the other. -/
partial def expr : P Expr :=
  letinxpr <|> funExpr <|> itexpr <|> matchExpr <|> forExpr <|> whileExpr <|> tryExpr
    <|> assignExpr

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

/-- `if c then t else e`. Without `else`, `e` is `()`. -/
partial def itexpr : P Expr := do
  keyword "if"
  let c ← expr
  keyword "then"
  let t ← expr
  let e ← (keyword "else" *> expr) <|> pure .unit
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

/-- `try e with p -> h | …`, see `tryWith`. -/
partial def tryExpr : P Expr := do
  keyword "try"
  let e ← seqExpr
  keyword "with"
  let _ ← option? (symbol "|")
  let arms ← sepBy1 (symbol "|") handler
  return tryWith e arms.toList

/-- One handler `p -> h` of a `try`. -/
partial def handler : P (Handler × Expr) := do
  let p ← (do let c ← ctorTok; let x ← binderTok <|> pure "_"; return Handler.tag c x)
    <|> (Handler.any <$> binderTok)
  symbol "->"
  let h ← seqExpr
  return (p, h)

-- The loops below desugar to a recursive function named `%for` / `%while`
/-- `for i = a to b do e done` is
    `let rec %for i = if i <= b then (e; %for (i + 1)) else () in %for a`. -/
partial def forExpr : P Expr := do
  keyword "for"
  let i ← binderTok
  symbol "="
  let a ← expr
  keyword "to"
  let b ← expr
  keyword "do"
  let e ← seqExpr
  keyword "done"
  let next := Expr.app (.var "%for") (.binop .add (.var i) (.int 1))
  return .letrec "%for" i (.ite (.binop .le (.var i) b) (.letin "_" e next) .unit)
    (.app (.var "%for") a)

/-- `while c do e done` is
    `let rec %while _ = if c then (e; %while ()) else () in %while ()`. -/
partial def whileExpr : P Expr := do
  keyword "while"
  let c ← expr
  keyword "do"
  let e ← seqExpr
  keyword "done"
  let next := Expr.app (.var "%while") .unit
  return .letrec "%while" "_" (.ite c (.letin "_" e next) .unit) next

/-- `a.(i) <- v`, `r := v`, or any other `orExpr`. -/
partial def assignExpr : P Expr := do
  let lhs ← orExpr
  let assignRef := do symbol ":="; let v ← expr; return Expr.assign lhs v
  match lhs with
  | .get a i => (do symbol "<-"; let v ← expr; return .set a i v) <|> assignRef <|> pure lhs
  | _ => assignRef <|> pure lhs

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
  (notFollowedBy (symbol "<-") *> cmpOp "<" .lt e) <|>
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

/-- `-e` (`0 - e`), `not e`, `assert e`, `Array.make n v`, `Array.length a`, and
    `ref v`, `incr r` / `decr r` (`r := !r ± 1`), `E v` and `raise e`. -/
partial def unary : P Expr :=
  (do
    let c ← ctorTok
    let v ← postfixExpr
    return .exn c v) <|>
  (do
    keyword "raise"
    let e ← unary
    return .raise e) <|>
  (do
    keyword "ref"
    let v ← postfixExpr
    return .ref 0 v) <|>
  (do
    keyword "incr"
    let r ← postfixExpr
    return .assign r (.binop .add (.deref r) (.int 1))) <|>
  (do
    keyword "decr"
    let r ← postfixExpr
    return .assign r (.binop .sub (.deref r) (.int 1))) <|>
  (do
    keyword "Array"; symbol "."; keyword "make"
    let n ← postfixExpr
    let v ← postfixExpr
    return .alloc 0 n v) <|>
  (do
    keyword "Array"; symbol "."; keyword "length"
    let a ← postfixExpr
    return .len a) <|>
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
  let f ← postfixExpr
  appRest f

partial def appRest (f : Expr) : P Expr :=
  (do let a ← postfixExpr; appRest (.app f a)) <|>
  pure f

/-- An atom followed by array reads `a.(i).(j)`. -/
partial def postfixExpr : P Expr := do
  let a ← atom
  getRest a

partial def getRest (a : Expr) : P Expr :=
  (do symbol "."; symbol "("; let i ← seqExpr; symbol ")"; getRest (.get a i)) <|>
  pure a

/-- Atoms: parenthesised expr, `()`, list literal, integer, boolean literal,
    variable, `!r`, or an exception without argument `E` (carrying `()`). -/
partial def atom : P Expr :=
  parenExpr
    <|> (do symbol "!"; let r ← atom; return .deref r)
    <|> (symbol "(" *> symbol ")" *> pure Expr.unit)
    <|> listLit
    <|> (Expr.int <$> intTok)
    <|> boolLit
    <|> (Expr.var <$> identTok)
    <|> (do let c ← ctorTok; return .exn c .unit)

/-- `[a; b; c]` is `a :: b :: c :: []`. -/
partial def listLit : P Expr := do
  symbol "["
  let es ← sepEndBy (symbol ";") expr
  symbol "]"
  return es.foldr .cons .nil

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

/-- A fresh allocation-site number. -/
def freshSite : StateM Nat Nat := modifyGet fun n => (n, n + 1)

/-- Number the allocation sites (`Array.make`, `ref`) 0, 1, 2, ... in source order.
    The parser leaves them all at 0.

    TODO: somehow avoid the pass
-/
def numberSites : Expr → StateM Nat Expr
  | .alloc _ n v => do
    let s ← freshSite
    return .alloc s (← numberSites n) (← numberSites v)
  | .ref _ v => do
    let s ← freshSite
    return .ref s (← numberSites v)
  | .app f a => return .app (← numberSites f) (← numberSites a)
  | .lam x b => return .lam x (← numberSites b)
  | .letin x a b => return .letin x (← numberSites a) (← numberSites b)
  | .letrec f x a b => return .letrec f x (← numberSites a) (← numberSites b)
  | .ite c t e => return .ite (← numberSites c) (← numberSites t) (← numberSites e)
  | .binop op a b => return .binop op (← numberSites a) (← numberSites b)
  | .cons a b => return .cons (← numberSites a) (← numberSites b)
  | .matchList s n x xs c =>
    return .matchList (← numberSites s) (← numberSites n) x xs (← numberSites c)
  | .assert c => return .assert (← numberSites c)
  | .get a i => return .get (← numberSites a) (← numberSites i)
  | .set a i v => return .set (← numberSites a) (← numberSites i) (← numberSites v)
  | .len a => return .len (← numberSites a)
  | .deref r => return .deref (← numberSites r)
  | .assign r v => return .assign (← numberSites r) (← numberSites v)
  | .exn c e => return .exn c (← numberSites e)
  | .raise e => return .raise (← numberSites e)
  | .tryw e x h => return .tryw (← numberSites e) x (← numberSites h)
  | .exnCase s c x h m =>
    return .exnCase (← numberSites s) c x (← numberSites h) (← numberSites m)
  | e => return e

/-- Parse a complete program. -/
def parse (s : String) : Except String Expr :=
  match (whitespace *> program <* endOfInput).parseString s with
  | .ok e => .ok ((numberSites e).run' 0)
  | .error err => .error s!"Parse error near byte {err.pos.byteIdx}"

end Diva
