import Lean.Data.Json
import Diva.Overflow
import Diva.TypeHints

/-!
# The C frontend (untrusted)

`diva c CMD file.c` runs clang (`clang -Xclang -ast-dump=json -fsyntax-only`), which
parses and type-checks the file, and prints its tree in JSON. `translate` translates the
tree to the items of DIVA's core language, with their positions, as the OCaml frontend
does. The program is the functions of the file, then the call `main ()`.

The C that is supported, so far: functions without parameters whose body is `return e;`,
where `e` is an expression on `int`s (literals, `+`, `-`, `*`, `/`, `%`). Anything else is
rejected, with its position.
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

/-- The operator of the C operator `op`, on `int`s. -/
def arith : String → Option BinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div
  | "%" => some .mod
  | _ => none

/-- The expression `t`, of type `int`. -/
partial def expr (t : Json) : M LExpr := do
  unless qualType t == "int" do unsupported t s!"the type `{qualType t}`"
  match kind t, inner t with
  | "IntegerLiteral", [] =>
    match (str t "value").bind String.toInt? with
    | some v => return ⟨.int v, .leaf (span t)⟩
    | none => unsupported t "this constant"
  | "ParenExpr", [a] => expr a
  -- a name read as a value
  | "ImplicitCastExpr", [a] =>
    if str t "castKind" == some "LValueToRValue" then expr a
    else unsupported t "this conversion"
  | "BinaryOperator", [a, b] =>
    match arith ((str t "opcode").getD "") with
    | some op =>
      let a ← expr a
      let b ← expr b
      return node t (.binop op a.expr b.expr) [a, b]
    | none => unsupported t s!"the operator `{(str t "opcode").getD ""}`"
  | "UnaryOperator", [a] =>
    match str t "opcode" with
    | some "+" => expr a
    | some "-" =>
      let a ← expr a
      let zero : LExpr := ⟨.int 0, .leaf (span t)⟩
      return node t (.binop .sub zero.expr a.expr) [zero, a]
    | op => unsupported t s!"the operator `{op.getD ""}`"
  | k, _ => unsupported t s!"this expression ({k})"

/-- The body of a function: `{ return e; }`. -/
def body (t : Json) : M LExpr :=
  match kind t, inner t with
  | "CompoundStmt", [s] =>
    match kind s, inner s with
    | "ReturnStmt", [e] => expr e
    | _, _ => unsupported s "this statement"
  | _, _ => unsupported t "this body (only `{ return e; }`)"

/-- The function `t`, as a top-level item: `let f = fun _ -> body`. -/
def function (t : Json) : M (String × Item × Loc) := do
  let some f := str t "name" | unsupported t "a function without a name"
  unless qualType t == "int (void)" do
    unsupported t s!"the type `{qualType t}` (only `int (void)`)"
  let some b := (inner t).getLast? | unsupported t "a function without a body"
  let b ← body b
  let e := node t (.lam "_" b.expr) [b]
  return (f, .decl (.val f e.expr) none, e.loc)

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
  let mut main : Option Span := none
  for d in ofFile path (inner tu) do
    match kind d with
    | "FunctionDecl" =>
      let (f, i, l) ← function d
      items := items.push (i, l)
      if f == "main" then main := some (nameSpan d)
    | _ => unsupported d "this declaration (only functions)"
  -- the call has the span of the name `main`
  let call := match main with
    | some sp => [(Item.expr (.app (.var "main") .unit), Loc.node sp [.leaf sp, .leaf sp])]
    | none => []
  return (items.toList ++ call, [])

/-- `msg` at the start of `sp` in the text `src` of the file: `line:col: msg`, with lines
    from 1 and columns from 0, as DIVA's own parser writes it. -/
def locate (src : String) (sp : Span) (msg : String) : String :=
  let (l, c) := lineCol src sp.start
  s!"{l}:{c}: {msg}"

end Diva.C
