import Lean.Data.Json
import Diva.Overflow
import Diva.TypeHints

/-!
# The C frontend (untrusted)

`diva c CMD file.c` runs clang (`clang -Xclang -ast-dump=json -fsyntax-only`), which
parses and type-checks the file, and prints its tree in JSON. `translate` translates the
tree to the items of DIVA's core language, with their positions, as the OCaml frontend
does. The program is the functions of the file, then the call `main ()`.

The C that is supported, so far: functions with `int` parameters whose body is
`return e;`, where `e` is an expression on `int`s (literals, parameters, `+`, `-`, `*`,
`/`, `%`). Each `+`, `-`, `*` and `/` checks that its result fits in an `int`: signed
overflow is undefined behaviour. Anything else is rejected, with its position.
-/

namespace Diva.C

open Lean (Json)

/-! ## The tree of clang -/

/-- The field `k` of the node `t`, if it has one. -/
def field (t : Json) (k : String) : Option Json := (t.getObjVal? k).toOption

/-- The string field `k` of `t`. -/
def str (t : Json) (k : String) : Option String := (field t k).bind (·.getStr?.toOption)

/-- The kind of the node `t`, such as `FunctionDecl` or `BinaryOperator`. -/
def kind (t : Json) : String := (str t "kind").getD ""

/-- The children of `t`. -/
def inner (t : Json) : List Json :=
  match field t "inner" with
  | some (.arr a) => a.toList
  | _ => []

/-- The C type of `t`, as clang writes it: `int`, or `int (int, int)` for a function. -/
def qualType (t : Json) : String := ((field t "type").bind (str · "qualType")).getD ""

/-- The part of the file of `t`: from the start of its first token to the end of its last
    token. -/
def span (t : Json) : Span :=
  let pos (k : String) := (field t "range").bind (field · k)
  let nat (p : Option Json) (k : String) := (p.bind (field · k)).bind (·.getNat?.toOption)
  let start := (nat (pos "begin") "offset").getD 0
  let last := (nat (pos "end") "offset").getD start
  ⟨start, last + (nat (pos "end") "tokLen").getD 0⟩

/-- The span of the name that the declaration `t` declares. -/
def nameSpan (t : Json) : Span :=
  let loc := field t "loc"
  let nat (k : String) := (loc.bind (field · k)).bind (·.getNat?.toOption)
  let start := (nat "offset").getD 0
  ⟨start, start + (nat "tokLen").getD 0⟩

/-! ## The translation -/

/-- The translation, which may stop on C that isn't supported: at the span of the code,
    with a message. -/
abbrev M := Except (Span × String)

/-- Stop on the node `t`, which DIVA doesn't support: `what` says what it is. -/
def unsupported (t : Json) (what : String) : M α :=
  throw (span t, s!"DIVA doesn't support {what}")

/-- `e` with the positions of `t`, and `kids` as its sub-expressions. -/
def node (t : Json) (e : Expr) (kids : List LExpr) : LExpr :=
  ⟨e, .node (span t) (kids.map (·.loc))⟩

/-- The names in scope: the id of their declaration in clang's tree, and their name in
    the core language. A name of C refers to its declaration by its id. -/
abbrev Env := List (String × String)

/-- The operator of the C operator `op`, on `int`s. -/
def arith : String → Option BinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div
  | "%" => some .mod
  | _ => none

/-- `e`, the operation `op` of the node `t`, with the check that its result fits in an
    `int` if it may not (`Overflow.wrap`): the overflow of a signed integer is undefined
    behaviour in C. -/
def checked (t : Json) (op : BinOp) (e : LExpr) : LExpr :=
  if Overflow.mayOverflow op then Overflow.wrap IntType.int32 e (span t) else e

/-- The expression `t`, of type `int`. `env` gives the names in scope. -/
partial def expr (env : Env) (t : Json) : M LExpr := do
  unless qualType t == "int" do unsupported t s!"the type `{qualType t}`"
  match kind t, inner t with
  | "IntegerLiteral", [] =>
    match (str t "value").bind String.toInt? with
    | some v => return ⟨.int v, .leaf (span t)⟩
    | none => unsupported t "this constant"
  | "ParenExpr", [a] => expr env a
  | "DeclRefExpr", [] =>
    match ((field t "referencedDecl").bind (str · "id")).bind (List.lookup · env) with
    | some x => return ⟨.var x, .leaf (span t)⟩
    | none => unsupported t "this name"
  -- a name read as a value
  | "ImplicitCastExpr", [a] =>
    if str t "castKind" == some "LValueToRValue" then expr env a
    else unsupported t "this conversion"
  | "BinaryOperator", [a, b] =>
    match arith ((str t "opcode").getD "") with
    | some op =>
      let a ← expr env a
      let b ← expr env b
      return checked t op (node t (.binop op a.expr b.expr) [a, b])
    | none => unsupported t s!"the operator `{(str t "opcode").getD ""}`"
  | "UnaryOperator", [a] =>
    match str t "opcode" with
    | some "+" => expr env a
    | some "-" =>
      let a ← expr env a
      let zero : LExpr := ⟨.int 0, .leaf (span t)⟩
      return checked t .sub (node t (.binop .sub zero.expr a.expr) [zero, a])
    | op => unsupported t s!"the operator `{op.getD ""}`"
  | k, _ => unsupported t s!"this expression ({k})"

/-- The body of a function: `{ return e; }`. -/
def body (env : Env) (t : Json) : M LExpr :=
  match kind t, inner t with
  | "CompoundStmt", [s] =>
    match kind s, inner s with
    | "ReturnStmt", [e] => expr env e
    | _, _ => unsupported s "this statement"
  | _, _ => unsupported t "this body (only `{ return e; }`)"

/-- The type `int` of C, for the hints of `--entry`: the integers of 32 bits. -/
def intTy : Ty := .range IntType.int32.min IntType.int32.max

/-- The function `t`, as a top-level item: `let f = fun x -> fun y -> body`, or
    `let f = fun _ -> body` without parameters. Also the types of its parameters, keyed
    by the span of their `fun`. -/
def function (t : Json) : M (String × Item × Loc × List TypeHint) := do
  let some f := str t "name" | unsupported t "a function without a name"
  unless (qualType t).startsWith "int (" do
    unsupported t s!"the type `{qualType t}` (only functions that return an `int`)"
  let params := (inner t).filter (kind · == "ParmVarDecl")
  let env ← params.mapM fun p => do
    unless qualType p == "int" do unsupported p s!"the type `{qualType p}`"
    let some id := str p "id" | unsupported p "a parameter without an id"
    let some x := str p "name" | unsupported p "a parameter without a name"
    return (id, x)
  let some b := (inner t).getLast? | unsupported t "a function without a body"
  let b ← body env b
  let names := if env.isEmpty then ["_"] else env.map (·.2)
  let e := names.foldr (fun x b => node t (.lam x b.expr) [b]) b
  let sp := span t
  let types := env.map fun (_, x) => { start := sp.start, stop := sp.stop, name := x, ty := intTy }
  return (f, .decl (.val f e.expr) none, e.loc, types)

/-- The declarations of the file `path` among the top-level declarations `decls` of
    clang's tree. clang writes the file of a position only when it changes from the
    previous position, so the current file is followed from one declaration to the next.
    The declarations that clang adds (`isImplicit`) are left out. -/
def ofFile (path : String) (decls : List Json) : List Json := Id.run do
  let mut file := ""
  let mut out := #[]
  for d in decls do
    let posns := [field d "loc", (field d "range").bind (field · "begin"),
      (field d "range").bind (field · "end")]
    for p in posns do
      if let some f := p.bind (str · "file") then file := f
    let implicit := ((field d "isImplicit").bind (·.getBool?.toOption)).getD false
    if !implicit && file == path then out := out.push d
  return out.toList

/-- The items of the program in the clang tree `tu` of the file `path`, with their
    positions, and the types of the parameters (for `--entry`). The functions, then
    `main ()` if there is a `main`. -/
def translate (tu : Json) (path : String) : M (List (Item × Loc) × List TypeHint) := do
  let mut items := #[]
  let mut types := #[]
  let mut main : Option Span := none
  for d in ofFile path (inner tu) do
    match kind d with
    | "FunctionDecl" =>
      let (f, i, l, ts) ← function d
      items := items.push (i, l)
      types := types ++ ts
      if f == "main" then main := some (nameSpan d)
    | _ => unsupported d "this declaration (only functions)"
  -- the call has the span of the name `main`
  let call := match main with
    | some sp => [(Item.expr (.app (.var "main") .unit), Loc.node sp [.leaf sp, .leaf sp])]
    | none => []
  return (items.toList ++ call, types.toList)

/-- `msg` at the start of `sp` in the text `src` of the file: `line:col: msg`, with lines
    from 1 and columns from 0, as DIVA's own parser writes it. -/
def locate (src : String) (sp : Span) (msg : String) : String :=
  let (l, c) := lineCol src sp.start
  s!"{l}:{c}: {msg}"

end Diva.C
