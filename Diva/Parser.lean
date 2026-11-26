import ParseIt
import Diva.Desugar
import Diva.Overflow

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

/-- A comment `(* ... *)`. Unlike OCaml, comments don't nest. A comment that starts
    with `(*@` is a contract (Gospel), so it isn't skipped: see `specComment`. -/
def comment : P Unit :=
  ParseIt.Char.string "(*" *> notFollowedBy (ParseIt.Char.string "@") *> dropUntil (ParseIt.Char.string "*)") anyToken *> pure ()

/-- Skip zero or more whitespace characters and comments. -/
def whitespace : P Unit := dropMany ((ASCII.whitespace *> pure ()) <|> comment) *> pure ()

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

/-- The pattern of a `try` handler: `E x` / `E` (an exception constructor), or `k` / `_`
    (any exception). -/
inductive Handler where
  | ctor : String → String → Handler
  | any : String → Handler

/-- `try e with p1 -> h1 | ... | pn -> hn` catches the exception as `%exn` (a name
    users cannot write), then tries the handlers in order.
    An exception no handler matches is raised again. -/
def tryWith (e : Expr) (arms : List (Handler × Expr)) : Expr :=
  .tryw e "%exn" (go arms)
where
  go : List (Handler × Expr) → Expr
    | [] => .raise (.var "%exn")
    | (.ctor c x, h) :: rest => .ctorCase (.var "%exn") c x h (go rest)
    | (.any k, h) :: _ => .letin k (.var "%exn") h

/-- The positions of `try e with ...` (`tryWith`), whose span is `sp`. `el` and the
    `Loc`s of `arms` are the positions of `e` and of the handlers. -/
def tryWithLoc (sp : Span) (el : Loc) (arms : List (Handler × Loc)) : Loc :=
  .node sp [el, go arms]
where
  go : List (Handler × Loc) → Loc
    | [] => .node sp [.leaf sp]
    | (.ctor _ _, h) :: rest => .node sp [.leaf sp, h, go rest]
    | (.any _, h) :: _ => .node sp [.leaf sp, h]

/-- The positions of `lams xs b` (`fun x1 -> ... -> b`): one node per `fun`, with the
    span `sp`, around the positions `bl` of `b`. -/
def lamsLoc (sp : Span) : List String → Loc → Loc
  | [], bl => bl
  | _ :: xs, bl => .node sp [lamsLoc sp xs bl]

/-- The current position, in bytes from the start of the source. -/
def pos : P Nat := do return (← getPos).byteIdx

/-- The span from the byte `s` to the current position. -/
def spanFrom (s : Nat) : P Span := do return ⟨s, ← pos⟩

/-! ### Expression grammar

Each rule gives the expression and its positions (`LExpr`). The children of a `Loc`
node follow the fields of the constructor (see `Loc.lean`). -/

mutual

/-- `e1; e2` is `let _ = e1 in e2`. -/
partial def seqExpr : P LExpr := do
  let s ← pos
  let e ← expr
  (do
    symbol ";"
    let r ← seqExpr
    return ⟨.letin "_" e.expr r.expr, .node (← spanFrom s) [e.loc, r.loc]⟩) <|> pure e

/-- A full expression, try to parse all constructors one after the other. -/
partial def expr : P LExpr :=
  letinxpr <|> funExpr <|> itexpr <|> matchExpr <|> forExpr <|> whileExpr <|> tryExpr
    <|> assignExpr

/-- `let [rec] f x y = e`, shared by `let ... in` and top-level declarations. With the
    positions of the expression bound to `f` (`fun x y -> e` for `let f x y = e`). -/
partial def binding : P (Binding × Loc) := do
  let s ← pos
  keyword "let"
  let isRec := (← option? (keyword "rec")).isSome
  let f ← binderTok
  let ps := (← takeMany binderTok).toList
  symbol "="
  let rhs ← seqExpr
  let sp ← spanFrom s
  match isRec, ps, rhs.expr with
  | false, _, _ => return (.val f (lams ps rhs.expr), lamsLoc sp ps rhs.loc)
  | true, x :: ps, _ => return (.recFn f x (lams ps rhs.expr), lamsLoc sp ps rhs.loc)
  | true, [], .lam x rhs' => return (.recFn f x rhs', rhs.loc.kid 0)
  | true, [], _ => throwUnexpected -- `let rec` must define a function

/-- `let x = e1 in e2` -/
partial def letinxpr : P LExpr := do
  let s ← pos
  let (b, bl) ← binding
  keyword "in"
  let e2 ← seqExpr
  return ⟨b.bind e2.expr, .node (← spanFrom s) [bl, e2.loc]⟩

/-- `fun x y -> e` -/
partial def funExpr : P LExpr := do
  let s ← pos
  keyword "fun"
  let xs ← takeMany1 binderTok
  symbol "->"
  let body ← seqExpr
  return ⟨lams xs.toList body.expr, lamsLoc (← spanFrom s) xs.toList body.loc⟩

/-- `if c then t else e`. Without `else`, `e` is `()`. -/
partial def itexpr : P LExpr := do
  let s ← pos
  keyword "if"
  let c ← expr
  keyword "then"
  let t ← expr
  let e ← (keyword "else" *> expr) <|> (do return ⟨.unit, .leaf (← spanFrom s)⟩)
  return ⟨.ite c.expr t.expr e.expr, .node (← spanFrom s) [c.loc, t.loc, e.loc]⟩

/-- `match s with [] -> n | x :: xs -> c` -/
partial def matchExpr : P LExpr := do
  let p ← pos
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
  return ⟨.matchList s.expr n.expr x xs c.expr, .node (← spanFrom p) [s.loc, n.loc, c.loc]⟩

/-- `try e with p -> h | ...`, see `tryWith`. -/
partial def tryExpr : P LExpr := do
  let s ← pos
  keyword "try"
  let e ← seqExpr
  keyword "with"
  let _ ← option? (symbol "|")
  let arms := (← sepBy1 (symbol "|") handler).toList
  return ⟨tryWith e.expr (arms.map fun (p, h) => (p, h.expr)),
    tryWithLoc (← spanFrom s) e.loc (arms.map fun (p, h) => (p, h.loc))⟩

/-- One handler `p -> h` of a `try`. -/
partial def handler : P (Handler × LExpr) := do
  let p ← (do let c ← ctorTok; let x ← binderTok <|> pure "_"; return Handler.ctor c x)
    <|> (Handler.any <$> binderTok)
  symbol "->"
  let h ← seqExpr
  return (p, h)

-- The loops below desugar to a recursive function named `%for` / `%while`. Names
-- starting with `%` can't be written in a program, so they capture nothing.
/-- `for i = a to b do e done` is
    `let %lo = a in let %hi = b in
     let rec %for i = if i <= %hi then (e; %for (i + 1)) else () in %for %lo`.
    The bounds are evaluated once, before the loop, as in OCaml. The code that this
    adds has the span of the whole loop. -/
partial def forExpr : P LExpr := do
  let s ← pos
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
  let loop := Expr.letrec "%for" i
    (.ite (.binop .le (.var i) (.var "%hi")) (.letin "_" e.expr next) .unit)
    (.app (.var "%for") (.var "%lo"))
  let sp ← spanFrom s
  let g := Loc.leaf sp
  let loopLoc := Loc.node sp [.node sp [g, .node sp [e.loc, g], g], g]
  return ⟨.letin "%lo" a.expr (.letin "%hi" b.expr loop),
    .node sp [a.loc, .node sp [b.loc, loopLoc]]⟩

/-- `while c do e done` is
    `let rec %while _ = if c then (e; %while ()) else () in %while ()`. -/
partial def whileExpr : P LExpr := do
  let s ← pos
  keyword "while"
  let c ← expr
  keyword "do"
  let e ← seqExpr
  keyword "done"
  let next := Expr.app (.var "%while") .unit
  let sp ← spanFrom s
  let g := Loc.leaf sp
  return ⟨.letrec "%while" "_" (.ite c.expr (.letin "_" e.expr next) .unit) next,
    .node sp [.node sp [c.loc, .node sp [e.loc, g], g], g]⟩

/-- `a.(i) <- v`, `r := v`, or any other `orExpr`. -/
partial def assignExpr : P LExpr := do
  let s ← pos
  let lhs ← orExpr
  let assignRef := do
    symbol ":="
    let v ← expr
    return ⟨Expr.assign lhs.expr v.expr, .node (← spanFrom s) [lhs.loc, v.loc]⟩
  match lhs.expr with
  | .get a i =>
    (do
      symbol "<-"
      let v ← expr
      return ⟨.set a i v.expr, .node (← spanFrom s) [lhs.loc.kid 0, lhs.loc.kid 1, v.loc]⟩)
    <|> assignRef <|> pure lhs
  | _ => assignRef <|> pure lhs

/-- `a || b` is `if a then true else b`. -/
partial def orExpr : P LExpr := do
  let s ← pos
  let a ← andExpr
  (do
    symbol "||"
    let b ← orExpr
    let sp ← spanFrom s
    return ⟨.ite a.expr (.bool true) b.expr, .node sp [a.loc, .leaf sp, b.loc]⟩) <|> pure a

/-- `a && b` is `if a then b else false`. -/
partial def andExpr : P LExpr := do
  let s ← pos
  let a ← cmpExpr
  (do
    symbol "&&"
    let b ← andExpr
    let sp ← spanFrom s
    return ⟨.ite a.expr b.expr (.bool false), .node sp [a.loc, b.loc, .leaf sp]⟩) <|> pure a

/-- `e sym r`, for the comparison `op`. `e` starts at the byte `s`. -/
partial def cmpOp (s : Nat) (sym: String) (op: BinOp) (e: LExpr) : P LExpr := do
  symbol sym
  let r ← pratt 0
  return ⟨.binop op e.expr r.expr, .node (← spanFrom s) [e.loc, r.loc]⟩

/-- Comparisons (non-associative). -/
partial def cmpExpr : P LExpr := do
  let s ← pos
  let e ← pratt 0
  (cmpOp s "=" .eq e) <|>
  (cmpOp s "<>" .ne e) <|>
  (cmpOp s "<=" .le e) <|>
  (notFollowedBy (symbol "<-") *> cmpOp s "<" .lt e) <|>
  (cmpOp s ">=" .ge e) <|>
  (cmpOp s ">" .gt e) <|>
  pure e

partial def pratt (lastBp: Nat) : P LExpr := do
  let s ← pos
  let lhs ← unary
  prattLoop s lhs lastBp

/-- The operators after `lhs`, which starts at the byte `s`. -/
partial def prattLoop (s : Nat) (lhs: LExpr) (lastBp: Nat) : P LExpr := (
    do
      let (builder, lbp, rbp) ← opbp
      -- compare with the binding power of the last op (default 0) only bind
      -- to current one if its >= lastBp
      if lbp < lastBp then
        throwUnexpected
      else
        let rhs ← pratt rbp
        let e : LExpr := ⟨builder lhs.expr rhs.expr, .node (← spanFrom s) [lhs.loc, rhs.loc]⟩
        prattLoop s e lastBp
  ) <|> pure lhs

/-- `-e` (`0 - e`), `not e`, `assert e`, `Array.make n v`, `Array.length a`, and
    `ref v`, `incr r` / `decr r` (`r := !r ± 1`), `E v` and `raise e`. -/
partial def unary : P LExpr := do
  let s ← pos
  -- `e` with the positions `.node span ks`, where `span` ends here
  let mk (e : Expr) (ks : Span → List Loc) : P LExpr := do
    let sp ← spanFrom s
    return ⟨e, .node sp (ks sp)⟩
  (do
    let c ← ctorTok
    let v ← postfixExpr
    mk (.ctor c v.expr) fun _ => [v.loc]) <|>
  (do
    keyword "raise"
    let e ← unary
    mk (.raise e.expr) fun _ => [e.loc]) <|>
  (do
    keyword "ref"
    let v ← postfixExpr
    mk (.ref 0 v.expr) fun _ => [v.loc]) <|>
  (do
    keyword "incr"
    let r ← postfixExpr
    mk (.assign r.expr (.binop .add (.deref r.expr) (.int 1)))
      fun sp => [r.loc, .node sp [.node sp [r.loc], .leaf sp]]) <|>
  (do
    keyword "decr"
    let r ← postfixExpr
    mk (.assign r.expr (.binop .sub (.deref r.expr) (.int 1)))
      fun sp => [r.loc, .node sp [.node sp [r.loc], .leaf sp]]) <|>
  (do
    keyword "Array"; symbol "."; keyword "make"
    let n ← postfixExpr
    let v ← postfixExpr
    mk (.alloc 0 n.expr v.expr) fun _ => [n.loc, v.loc]) <|>
  (do
    keyword "Array"; symbol "."; keyword "length"
    let a ← postfixExpr
    mk (.len a.expr) fun _ => [a.loc]) <|>
  (do
    symbol "-"
    let e ← unary
    mk (.binop .sub (.int 0) e.expr) fun sp => [.leaf sp, e.loc]) <|>
  (do
    keyword "not"
    let e ← unary
    mk (.ite e.expr (.bool false) (.bool true)) fun sp => [e.loc, .leaf sp, .leaf sp]) <|>
  (do
    keyword "assert"
    let e ← unary
    mk (.assert e.expr) fun _ => [e.loc]) <|>
  appExpr

/-- Left-associative application `e e e ...`. -/
partial def appExpr : P LExpr := do
  let s ← pos
  let f ← postfixExpr
  appRest s f

/-- The arguments after `f`, which starts at the byte `s`. -/
partial def appRest (s : Nat) (f : LExpr) : P LExpr :=
  (do
    let a ← postfixExpr
    appRest s ⟨.app f.expr a.expr, .node (← spanFrom s) [f.loc, a.loc]⟩) <|>
  pure f

/-- An atom followed by array reads `a.(i).(j)`. -/
partial def postfixExpr : P LExpr := do
  let s ← pos
  let a ← atom
  getRest s a

/-- The array reads after `a`, which starts at the byte `s`. -/
partial def getRest (s : Nat) (a : LExpr) : P LExpr :=
  (do
    symbol "."; symbol "("
    let i ← seqExpr
    symbol ")"
    getRest s ⟨.get a.expr i.expr, .node (← spanFrom s) [a.loc, i.loc]⟩) <|>
  pure a

/-- Atoms: parenthesised expr, `()`, list literal, integer, boolean literal,
    variable, `!r`, or an exception without argument `E` (carrying `()`). -/
partial def atom : P LExpr := do
  let s ← pos
  let leaf (e : Expr) : P LExpr := do return ⟨e, .leaf (← spanFrom s)⟩
  parenExpr
    <|> (do symbol "!"; let r ← atom; return ⟨.deref r.expr, .node (← spanFrom s) [r.loc]⟩)
    <|> (do symbol "("; symbol ")"; leaf .unit)
    <|> listLit
    <|> (do leaf (.int (← intTok)))
    <|> boolLit
    <|> (do leaf (.var (← identTok)))
    <|> (do let c ← ctorTok; leaf (.ctor c .unit))

/-- `[a; b; c]` is `a :: b :: c :: []`. Each `::` has the span of the whole list. -/
partial def listLit : P LExpr := do
  let s ← pos
  symbol "["
  let es ← sepEndBy (symbol ";") expr
  symbol "]"
  let sp ← spanFrom s
  return es.foldr (fun a r => ⟨.cons a.expr r.expr, .node sp [a.loc, r.loc]⟩)
    ⟨.nil, .leaf sp⟩

/-- `( e )` -/
partial def parenExpr : P LExpr := do
  symbol "("
  let e ← seqExpr
  symbol ")"
  return e

/-- `true` / `false` -/
partial def boolLit : P LExpr := do
  let s ← pos
  let b ← (keyword "true" *> pure true) <|> (keyword "false" *> pure false)
  return ⟨.bool b, .leaf (← spanFrom s)⟩

end

/-! ### Contracts (Gospel)

A contract follows a top-level function, in a comment that starts with `(*@`:
```
let rec sum n = if n <= 0 then 0 else n + sum (n - 1)
(*@ r = sum n
    requires n >= 0
    ensures r >= 0 *)
```
-/

/-- A name in a contract. `requires` and `ensures` start a clause, so they aren't
    names. -/
def specIdent : P String := do
  let x ← identTok
  if x == "requires" || x == "ensures" then throwUnexpected else pure x

mutual

/-- `a && b` (also written `a /\ b`), or a comparison. -/
partial def term : P Term := do
  let a ← cmpTerm
  (do (symbol "&&" <|> symbol "/\\"); let b ← term; return .and a b) <|> pure a

/-- `a op b` for a comparison `op`, or `a`. -/
partial def cmpTerm : P Term := do
  let a ← sumTerm
  let op ← option? ((symbol "=" *> pure BinOp.eq) <|> (symbol "<>" *> pure .ne) <|>
    (symbol "<=" *> pure .le) <|> (symbol "<" *> pure .lt) <|>
    (symbol ">=" *> pure .ge) <|> (symbol ">" *> pure .gt))
  match op with
  | some op => return .binop op a (← sumTerm)
  | none => return a

/-- `a + b - c ...`, left-associative. -/
partial def sumTerm : P Term := do
  sumRest (← mulTerm)

partial def sumRest (a : Term) : P Term :=
  (do symbol "+"; let b ← mulTerm; sumRest (.binop .add a b)) <|>
  (do symbol "-"; let b ← mulTerm; sumRest (.binop .sub a b)) <|>
  pure a

/-- `a * b * c ...`, left-associative. -/
partial def mulTerm : P Term := do
  mulRest (← atomTerm)

/-- The `*` of the `*)` that ends the contract isn't a product. -/
partial def mulRest (a : Term) : P Term :=
  (do notFollowedBy (symbol "*)"); symbol "*"; let b ← atomTerm; mulRest (.binop .mul a b))
  <|> pure a

/-- An integer, a name, `( t )`, or `-t` (`0 - t`). -/
partial def atomTerm : P Term :=
  (Term.int <$> intTok) <|> (Term.var <$> specIdent) <|>
  (do symbol "("; let t ← term; symbol ")"; return t) <|>
  (do symbol "-"; let t ← atomTerm; return .binop .sub (.int 0) t)

end

/-- The header `r = f x` of a contract: the names of the result, the function and the
    parameters. -/
def specHeader : P (String × String × List String) := do
  let r ← specIdent
  symbol "="
  let f ← specIdent
  let xs ← takeMany specIdent
  return (r, f, xs.toList)

/-- A clause `requires t` (`true`) or `ensures t` (`false`). -/
def clause : P (Bool × Term) :=
  (do keyword "requires"; return (true, ← term)) <|>
  (do keyword "ensures"; return (false, ← term))

/-- A contract `(*@ r = f x requires ... ensures ... *)`. The header is optional. -/
def specComment : P Spec := do
  symbol "(*@"
  let header ← option? specHeader
  let clauses := (← takeMany clause).toList
  symbol "*)"
  let (result, name, params) := match header with
    | some (r, f, xs) => (r, some f, xs)
    | none => ("result", none, [])
  return { result, name, params,
           requires := clauses.filterMap fun (r, t) => if r then some t else none,
           ensures := clauses.filterMap fun (r, t) => if r then none else some t }

/-- A declaration, with the contract after it, and the positions of the expression
    that it binds. -/
def declItem : P (Item × Loc) := do
  let (b, l) ← binding
  let s ← option? specComment
  return (.decl b s, l)

/-- A top-level item, with its positions. -/
def item : P (Item × Loc) :=
  (do let e ← letinxpr; return (Item.expr e.expr, e.loc)) <|>
  declItem <|>
  (do let e ← seqExpr; return (Item.expr e.expr, e.loc))

/-- The top-level items of a program.
    As in OCaml, `;;` is optional between declarations but required before an
    expression that isn't first. -/
def itemsLoc : P (List (Item × Loc)) := do
  let _ ← dropMany (symbol ";;")
  let first ← option? item
  let rest ← takeMany (declItem <|> (takeMany1 (symbol ";;") *> item))
  let _ ← dropMany (symbol ";;")
  return first.toList ++ rest.toList

/-- The top-level items of a program, without their positions. -/
def items : P (List Item) := (·.map (·.1)) <$> itemsLoc

/-- A program: its top-level items, as one expression, with its positions. -/
def program : P LExpr := do
  let is ← itemsLoc
  return ⟨Item.toExpr (is.map (·.1)), Item.toLoc is⟩

/-- The state of `resolve`: the next site number and the next name number. -/
structure Fresh where
  /-- The next allocation-site number. -/
  site : Nat := 0
  /-- The next number for a function parameter or recursive-function name. -/
  name : Nat := 0

/-- A fresh allocation-site number. -/
def freshSite : StateM Fresh Nat :=
  modifyGet fun s => (s.site, { s with site := s.site + 1 })

/-- A fresh name `x#n` for the parameter or recursive function `x`. `#` can't appear
    in an identifier, so `x#n` is unique. -/
def freshName (x : String) : StateM Fresh String :=
  modifyGet fun s => (s!"{x}#{s.name}", { s with name := s.name + 1 })

/-- The pass after parsing:
    - number the allocation sites (`Array.make`, `ref`) 0, 1, 2, ... in source order
      (the parser leaves them at 0);
    - give every function parameter and recursive function a name of its own. The
      analysis keys its hints by these names, so two functions with a parameter `y`
      would otherwise share one precondition.

    `sc` maps each variable in scope to its new name. -/
def resolve (sc : List (String × String)) : Expr → StateM Fresh Expr
  | .var x => return .var ((sc.lookup x).getD x)
  | .lam x b => do
    let x' ← freshName x
    return .lam x' (← resolve ((x, x') :: sc) b)
  | .letrec f x b e2 => do
    let f' ← freshName f
    let x' ← freshName x
    return .letrec f' x' (← resolve ((x, x') :: (f, f') :: sc) b) (← resolve ((f, f') :: sc) e2)
  -- the other binders keep their name, but hide an outer variable of that name
  | .letin x a b => return .letin x (← resolve sc a) (← resolve ((x, x) :: sc) b)
  | .matchList s n x xs c =>
    return .matchList (← resolve sc s) (← resolve sc n) x xs
      (← resolve ((xs, xs) :: (x, x) :: sc) c)
  | .tryw e k h => return .tryw (← resolve sc e) k (← resolve ((k, k) :: sc) h)
  | .ctorCase s c x h m =>
    return .ctorCase (← resolve sc s) c x (← resolve ((x, x) :: sc) h) (← resolve sc m)
  | .alloc _ n v => do
    let s ← freshSite
    return .alloc s (← resolve sc n) (← resolve sc v)
  | .ref _ v => do
    let s ← freshSite
    return .ref s (← resolve sc v)
  | .app f a => return .app (← resolve sc f) (← resolve sc a)
  | .ite c t e => return .ite (← resolve sc c) (← resolve sc t) (← resolve sc e)
  | .binop op a b => return .binop op (← resolve sc a) (← resolve sc b)
  | .cons a b => return .cons (← resolve sc a) (← resolve sc b)
  | .assert c => return .assert (← resolve sc c)
  | .get a i => return .get (← resolve sc a) (← resolve sc i)
  | .set a i v => return .set (← resolve sc a) (← resolve sc i) (← resolve sc v)
  | .len a => return .len (← resolve sc a)
  | .deref r => return .deref (← resolve sc r)
  | .assign r v => return .assign (← resolve sc r) (← resolve sc v)
  | .ctor c e => return .ctor c (← resolve sc e)
  | .raise e => return .raise (← resolve sc e)
  | e => return e

/-- Where the parser stopped in `s`, as `line:col: parse error`. -/
def errorAt (s : String) (off : Nat) : String :=
  let (l, c) := lineCol s off
  s!"{l}:{c}: parse error"

/-- How a command gets the program from the text of a file: its top-level items with
    their positions, or an error. DIVA's parser is one (`parseItemsLoc`). The OCaml
    frontend is another (`Sexp.items`). -/
abbrev Reader := String → Except String (List (Item × Loc))

/-- Parse a complete program into its top-level items, with their positions. -/
def parseItemsLoc : Reader := fun s =>
  match (whitespace *> itemsLoc <* endOfInput).parseString s with
  | .ok is => .ok is
  | .error err => .error (errorAt s err.pos.byteIdx)

/-- The reader `r`, where each operation that may overflow the integer type `intTy` is
    checked (`Overflow.items`). Without `intTy`, `r` itself. An integer literal that
    doesn't fit in `intTy` is an error. -/
def Reader.withIntTy (intTy : Option IntType) (r : Reader) : Reader := fun s =>
  (r s).bind (Overflow.items intTy s)

/-- The program read by `r`, as one expression, with its positions. `resolve` keeps
    the shape of the expression, so the positions stay valid. -/
def Reader.lexpr (r : Reader) (s : String) : Except String LExpr :=
  (r s).map fun is => ⟨(resolve [] (Item.toExpr (is.map (·.1)))).run' {}, Item.toLoc is⟩

/-- The program read by `r`, as one expression. -/
def Reader.expr (r : Reader) (s : String) : Except String Expr :=
  (r.lexpr s).map (·.expr)

/-- The top-level items read by `r`, with their contracts. The names are the ones of
    the source: there is no `resolve`. -/
def Reader.items (r : Reader) (s : String) : Except String (List Item) :=
  (r s).map (·.map (·.1))

/-- Parse a complete program, with its positions. -/
def parseLoc : String → Except String LExpr := parseItemsLoc.lexpr

/-- Parse a complete program. -/
def parse : String → Except String Expr := parseItemsLoc.expr

/-- Parse a formula of the contract language, such as `0 <= v && v < 10`. -/
def parseTerm (s : String) : Except String Term :=
  match (whitespace *> term <* endOfInput).parseString s with
  | .ok t => .ok t
  | .error err => .error (errorAt s err.pos.byteIdx)

/-- Parse a contract `(*@ ... *)`. -/
def parseSpec (s : String) : Except String Spec :=
  match (whitespace *> specComment <* endOfInput).parseString s with
  | .ok sp => .ok sp
  | .error err => .error (errorAt s err.pos.byteIdx)

/-- Parse a complete program into its top-level items, with their contracts. -/
def parseItems : String → Except String (List Item) := parseItemsLoc.items

end Diva
