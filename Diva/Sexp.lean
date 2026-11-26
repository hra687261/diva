import Diva.Parser

/-!
# Programs as S-expressions (untrusted)

The OCaml front end (`frontend/ocaml/frontend.ml`) prints the program that it
translates as S-expressions. This module reads them into the top-level items of a
program, with their positions, as DIVA's parser does (`Reader`).

```
PROGRAM ::= (program ITEM ...)
ITEM    ::= (let "f" EXPR [SPEC])        let f = e
          | (letrec "f" "x" EXPR [SPEC])  let rec f x = e
          | (expr EXPR)                   ;; e
SPEC    ::= "(*@ ... *)"                  the text of the contract
```

The text of a contract may start with spaces and newlines. The front end adds them
so that the positions in the contract are those of the file.

Each `EXPR` is one constructor of `Expr`, with the part of the source it comes from:
the bytes `START` to `STOP` of the OCaml file. Names are strings.

```
(int START STOP N)   (bool START STOP true|false)   (unit START STOP)   (nil START STOP)
(var START STOP "x")   (app START STOP F A)   (lam START STOP "x" B)
(letin START STOP "x" E1 E2)   (letrec START STOP "f" "x" B E2)
(ite START STOP C T E)   (binop START STOP OP A B)   (cons START STOP A B)
(matchList START STOP S N "x" "xs" C)   (assert START STOP C)
(alloc START STOP N V)   (get START STOP A I)   (set START STOP A I V)   (len START STOP A)
(ref START STOP V)   (deref START STOP R)   (assign START STOP R V)
(exn START STOP "C" V)   (raise START STOP V)   (tryw START STOP A "k" H)
(exnCase START STOP S "C" "x" H M)
OP ::= add | sub | mul | div | mod | eq | ne | lt | le | gt | ge
```

`alloc` and `ref` have no allocation site: `resolve` numbers them.

`(overflow START STOP BITS E)` says that `E` computes an integer of `BITS` bits. It is `E`,
followed by the check that its value fits (`Overflow.wrap`), if it may not: an operation
that can't overflow (`Overflow.mayOverflow`), such as `mod`, isn't checked.
-/

namespace Diva

/-- An S-expression: a word, a string in quotes, or a list in parentheses. -/
inductive Sexp where
  | atom : String → Sexp
  | str : String → Sexp
  | list : List Sexp → Sexp
  deriving Inhabited, Repr, BEq

namespace Sexp

/-- The text of an S-expression, for error messages. -/
partial def text : Sexp → String
  | .atom a => a
  | .str s => s!"\"{s}\""
  | .list xs => "(" ++ " ".intercalate (xs.map text) ++ ")"

/-- The characters of a word: anything but spaces, parentheses and quotes. -/
def isWordChar (c : Char) : Bool :=
  !c.isWhitespace && c != '(' && c != ')' && c != '"'

/-- The S-expression at the start of `cs`, and the characters after it. -/
partial def parseOne : List Char → Except String (Sexp × List Char)
  | [] => .error "an S-expression ends too early"
  | c :: cs =>
    if c.isWhitespace then parseOne cs
    else if c == '(' then do
      let (xs, rest) ← parseList cs []
      return (.list xs, rest)
    else if c == ')' then .error "unexpected `)`"
    else if c == '"' then do
      let (s, rest) ← parseStr cs ""
      return (.str s, rest)
    else
      let word := (c :: cs).takeWhile isWordChar
      return (.atom (String.ofList word), (c :: cs).dropWhile isWordChar)
where
  /-- The elements of a list until its `)`, after `acc`. -/
  parseList (cs : List Char) (acc : List Sexp) : Except String (List Sexp × List Char) :=
    match cs.dropWhile Char.isWhitespace with
    | ')' :: rest => .ok (acc.reverse, rest)
    | [] => .error "a list has no `)`"
    | cs => do
      let (x, rest) ← parseOne cs
      parseList rest (x :: acc)
  /-- The rest of a string after `acc`, until its closing quote. `\"` and `\\` are a
      quote and a backslash. -/
  parseStr (cs : List Char) (acc : String) : Except String (String × List Char) :=
    match cs with
    | '"' :: rest => .ok (acc, rest)
    | '\\' :: c :: rest => parseStr rest (acc.push c)
    | c :: rest => parseStr rest (acc.push c)
    | [] => .error "a string has no closing quote"

/-- The S-expression of the whole text `s`. -/
def parse (s : String) : Except String Sexp := do
  let (x, rest) ← parseOne s.toList
  if rest.all Char.isWhitespace then return x
  else .error "text after the S-expression"

/-- A natural number. -/
def nat : Sexp → Except String Nat
  | .atom a => match a.toNat? with
    | some n => .ok n
    | none => .error s!"`{a}` is not a natural number"
  | x => .error s!"`{x.text}` is not a natural number"

/-- An integer, maybe negative. -/
def int : Sexp → Except String Int
  | .atom a => match a.toInt? with
    | some n => .ok n
    | none => .error s!"`{a}` is not an integer"
  | x => .error s!"`{x.text}` is not an integer"

/-- A name, in quotes. -/
def name : Sexp → Except String String
  | .str s => .ok s
  | x => .error s!"`{x.text}` is not a name in quotes"

def binOp : Sexp → Except String BinOp
  | .atom "add" => .ok .add | .atom "sub" => .ok .sub | .atom "mul" => .ok .mul
  | .atom "div" => .ok .div | .atom "mod" => .ok .mod | .atom "eq" => .ok .eq
  | .atom "ne" => .ok .ne | .atom "lt" => .ok .lt | .atom "le" => .ok .le
  | .atom "gt" => .ok .gt | .atom "ge" => .ok .ge
  | x => .error s!"`{x.text}` is not an operator"

/-- The expression of `x`, with its positions. -/
partial def expr (x : Sexp) : Except String LExpr := do
  let .list (.atom k :: start :: stop :: args) := x
    | .error s!"`{x.text}` is not an expression"
  let span : Span := ⟨← nat start, ← nat stop⟩
  -- the expression `e`, whose sub-expressions have the positions `ls`
  let node (e : Expr) (ls : List LExpr) : LExpr := ⟨e, .node span (ls.map (·.loc))⟩
  match k, args with
  | "int", [n] => return node (.int (← int n)) []
  | "bool", [.atom "true"] => return node (.bool true) []
  | "bool", [.atom "false"] => return node (.bool false) []
  | "unit", [] => return node .unit []
  | "nil", [] => return node .nil []
  | "var", [y] => return node (.var (← name y)) []
  | "app", [f, a] =>
    let f ← expr f
    let a ← expr a
    return node (.app f.expr a.expr) [f, a]
  | "lam", [y, b] =>
    let b ← expr b
    return node (.lam (← name y) b.expr) [b]
  | "letin", [y, e1, e2] =>
    let e1 ← expr e1
    let e2 ← expr e2
    return node (.letin (← name y) e1.expr e2.expr) [e1, e2]
  | "letrec", [f, y, b, e2] =>
    let b ← expr b
    let e2 ← expr e2
    return node (.letrec (← name f) (← name y) b.expr e2.expr) [b, e2]
  | "ite", [c, t, e] =>
    let c ← expr c
    let t ← expr t
    let e ← expr e
    return node (.ite c.expr t.expr e.expr) [c, t, e]
  | "binop", [op, a, b] =>
    let a ← expr a
    let b ← expr b
    return node (.binop (← binOp op) a.expr b.expr) [a, b]
  | "cons", [a, b] =>
    let a ← expr a
    let b ← expr b
    return node (.cons a.expr b.expr) [a, b]
  | "matchList", [s, n, y, ys, c] =>
    let s ← expr s
    let n ← expr n
    let c ← expr c
    return node (.matchList s.expr n.expr (← name y) (← name ys) c.expr) [s, n, c]
  | "assert", [c] =>
    let c ← expr c
    return node (.assert c.expr) [c]
  | "alloc", [n, v] =>
    let n ← expr n
    let v ← expr v
    return node (.alloc 0 n.expr v.expr) [n, v]
  | "get", [a, i] =>
    let a ← expr a
    let i ← expr i
    return node (.get a.expr i.expr) [a, i]
  | "set", [a, i, v] =>
    let a ← expr a
    let i ← expr i
    let v ← expr v
    return node (.set a.expr i.expr v.expr) [a, i, v]
  | "len", [a] =>
    let a ← expr a
    return node (.len a.expr) [a]
  | "ref", [v] =>
    let v ← expr v
    return node (.ref 0 v.expr) [v]
  | "deref", [r] =>
    let r ← expr r
    return node (.deref r.expr) [r]
  | "assign", [r, v] =>
    let r ← expr r
    let v ← expr v
    return node (.assign r.expr v.expr) [r, v]
  | "exn", [c, v] =>
    let v ← expr v
    return node (.exn (← name c) v.expr) [v]
  | "raise", [v] =>
    let v ← expr v
    return node (.raise v.expr) [v]
  | "tryw", [a, y, h] =>
    let a ← expr a
    let h ← expr h
    return node (.tryw a.expr (← name y) h.expr) [a, h]
  | "exnCase", [s, c, y, h, m] =>
    let s ← expr s
    let h ← expr h
    let m ← expr m
    return node (.exnCase s.expr (← name c) (← name y) h.expr m.expr) [s, h, m]
  | "overflow", [bits, e] =>
    let e ← expr e
    let t : IntType := ⟨← nat bits⟩
    -- an operation whose result always fits, such as `mod` or a comparison, isn't checked
    return match e.expr with
      | .binop op _ _ => if Overflow.mayOverflow op then Overflow.wrap t e span else e
      | _ => Overflow.wrap t e span
  | _, _ => .error s!"`{x.text}` is not an expression"

/-- The contract of a declaration, if it has one. -/
def spec : List Sexp → Except String (Option Spec)
  | [] => .ok none
  | [.str s] => (parseSpec s).map some
  | xs => .error s!"`{(Sexp.list xs).text}` is not a contract"

/-- A top-level item, with the positions of its expression. -/
def item (x : Sexp) : Except String (Item × Loc) := do
  match x with
  | .list (.atom "let" :: f :: e :: sp) =>
    let e ← expr e
    return (.decl (.val (← name f) e.expr) (← spec sp), e.loc)
  | .list (.atom "letrec" :: f :: y :: e :: sp) =>
    let e ← expr e
    return (.decl (.recFn (← name f) (← name y) e.expr) (← spec sp), e.loc)
  | .list [.atom "expr", e] =>
    let e ← expr e
    return (.expr e.expr, e.loc)
  | _ => .error s!"`{x.text}` is not a top-level item"

/-- The items of the program printed in `s`. -/
def items (s : String) : Except String (List (Item × Loc)) := do
  match ← parse s with
  | .list (.atom "program" :: xs) => xs.mapM item
  | x => .error s!"`{x.text}` is not a program"

end Sexp

end Diva
