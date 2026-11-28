import Lean.Data.Json
import Diva.Overflow
import Diva.TypeHints

/-!
# The C frontend (untrusted)

`diva c CMD file.c` runs clang (`clang -Xclang -ast-dump=json -fsyntax-only`), which
parses and type-checks the file, and prints its tree in JSON. `translate` translates the
tree to the items of DIVA's core language, with their positions, as the OCaml frontend
does. The program is the functions of the file, then the call `main ()`.

The C that is supported, so far: functions with `int` parameters, whose bodies have
locals of type `int`, assignments to them (`=`, `+=`, `++`, ...) and `return`, and
expressions on `int`s (literals, parameters, `+`, `-`, `*`,
`/`, `%`, comparisons, `&&`, `||`, `!`, `c ? a : b`). Each `+`, `-`, `*` and `/` checks that
its result fits in an `int`: signed overflow is undefined behaviour. `a % b` checks that
`a / b` fits (only `INT_MIN % -1` doesn't). A condition is a boolean of the core language:
a comparison, or `c != 0` for another `int`. A condition used as a value is `1` or `0`.
Anything else is rejected, with its position.
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

/-- `a % b` of the node `t`, with the check that `a / b` fits in an `int`: C leaves `a % b`
    undefined when `a / b` doesn't fit (C11, 6.5.5), which is `INT_MIN % -1`. So `a % b` is
    `let %a = a in let %b = b in assert (if %a = INT_MIN then %b <> -1 else true); %a mod %b`.
    -/
def remChecked (t : Json) (a b : LExpr) : LExpr :=
  let leaf (e : Expr) : LExpr := ⟨e, .leaf (span t)⟩
  let letin (x : String) (e rest : LExpr) := node t (.letin x e.expr rest.expr) [e, rest]
  -- `%a = INT_MIN`
  let isMin := node t (.binop .eq (.var "%a") (.int IntType.int32.min))
    [leaf (.var "%a"), leaf (.int IntType.int32.min)]
  -- `%b <> -1`
  let notM1 := node t (.binop .ne (.var "%b") (.int (-1))) [leaf (.var "%b"), leaf (.int (-1))]
  -- `assert (if %a = INT_MIN then %b <> -1 else true)`
  let ok := node t (.ite isMin.expr notM1.expr (.bool true)) [isMin, notM1, leaf (.bool true)]
  let check := node t (.assert ok.expr) [ok]
  -- `%a mod %b`, after the check
  let rem := node t (.binop .mod (.var "%a") (.var "%b")) [leaf (.var "%a"), leaf (.var "%b")]
  -- `a` and `b` are computed once, before the check
  letin "%a" a (letin "%b" b (letin "_" check rem))

/-- The comparison of C `op`, on `int`s: its result is a boolean of the core language. -/
def cmp : String → Option BinOp
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "==" => some .eq | "!=" => some .ne
  | _ => none

/-- The node `t` is a condition of C: a comparison, `&&`, `||` or `!`. Its value is `0` or
    `1`, and `cond` gives it as a boolean. -/
def isCond (t : Json) : Bool :=
  match kind t, str t "opcode" with
  | "BinaryOperator", some op => (cmp op).isSome || op == "&&" || op == "||"
  | "UnaryOperator", some "!" => true
  | _, _ => false

/-- `if c then a else b`, with the positions of `t`. -/
def ite (t : Json) (c a b : LExpr) : LExpr := node t (.ite c.expr a.expr b.expr) [c, a, b]

/-- The boolean `b`, with the positions of `t`. -/
def bool (t : Json) (b : Bool) : LExpr := ⟨.bool b, .leaf (span t)⟩

/-- The integer `v`, with the positions of `t`. -/
def int (t : Json) (v : Int) : LExpr := ⟨.int v, .leaf (span t)⟩

mutual

/-- The expression `t`, of type `int`. `env` gives the names in scope. -/
partial def expr (env : Env) (t : Json) : M LExpr := do
  unless qualType t == "int" do unsupported t s!"the type `{qualType t}`"
  -- a condition used as a value: `1` if it holds, else `0`
  if isCond t then return ite t (← cond env t) (int t 1) (int t 0)
  match kind t, inner t with
  | "IntegerLiteral", [] =>
    match (str t "value").bind String.toInt? with
    | some v => return int t v
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
      if op == .mod then return remChecked t a b
      return checked t op (node t (.binop op a.expr b.expr) [a, b])
    | none => unsupported t s!"the operator `{(str t "opcode").getD ""}`"
  | "UnaryOperator", [a] =>
    match str t "opcode" with
    | some "+" => expr env a
    | some "-" =>
      let a ← expr env a
      let zero := int t 0
      return checked t .sub (node t (.binop .sub zero.expr a.expr) [zero, a])
    | op => unsupported t s!"the operator `{op.getD ""}`"
  -- `c ? a : b`
  | "ConditionalOperator", [c, a, b] => return ite t (← cond env c) (← expr env a) (← expr env b)
  | k, _ => unsupported t s!"this expression ({k})"

/-- The condition `t` as a boolean: a comparison, `&&` and `||` (which compute their right
    side only if they need it), `!`, or an `int` that holds if it isn't `0`. -/
partial def cond (env : Env) (t : Json) : M LExpr := do
  match kind t, str t "opcode", inner t with
  | "ParenExpr", _, [a] => cond env a
  | "BinaryOperator", some "&&", [a, b] => return ite t (← cond env a) (← cond env b) (bool t false)
  | "BinaryOperator", some "||", [a, b] => return ite t (← cond env a) (bool t true) (← cond env b)
  | "UnaryOperator", some "!", [a] => return ite t (← cond env a) (bool t false) (bool t true)
  | "BinaryOperator", some op, [a, b] =>
    match cmp op with
    | some op =>
      let a ← expr env a
      let b ← expr env b
      return node t (.binop op a.expr b.expr) [a, b]
    | none => ne0 t
  | _, _, _ => ne0 t
where
  /-- `t != 0`. -/
  ne0 (t : Json) : M LExpr := do
    let a ← expr env t
    let zero := int t 0
    return node t (.binop .ne a.expr zero.expr) [a, zero]

end

/-! ## Statements

A statement is translated with the code that comes after it, its continuation `k`
(continuation-passing style): `int x = e; rest` is `let x = e in rest`. Each local of a
function has its own name in the core language, so a local that hides another one in a
block gets another name, and the code after the block sees the first one again. An
assignment `x = e;` binds the name of `x` again: `let x = e in rest`. `return e;` gives
`e`, without its continuation. -/

/-- The translation of statements, which also gives each local of the function its own
    name: the state is the names used so far. -/
abbrev S := StateT (List String) M

/-- A name for the local `x` that the function doesn't use yet: `x`, else `x%2`, ... -/
def fresh (x : String) : S String := do
  let used ← get
  let t := (used.filter fun u => u == x || u.startsWith (x ++ "%")).length
  let y := if t == 0 then x else s!"{x}%{t + 1}"
  set (y :: used)
  return y

/-- `let x = e in rest`, with the positions of `t`. -/
def letin (t : Json) (x : String) (e rest : LExpr) : LExpr :=
  node t (.letin x e.expr rest.expr) [e, rest]

/-- The name of the local that `t` refers to (`DeclRefExpr`), with the casts of clang
    around it. -/
partial def local? (env : Env) (t : Json) : Option String :=
  match kind t, inner t with
  | "DeclRefExpr", [] => ((field t "referencedDecl").bind (str · "id")).bind (List.lookup · env)
  | "ParenExpr", [a] => local? env a
  | _, _ => none

/-- The expression statement `t`: an assignment to a local (`x = e`, `x += e`, `x++`,
    `--x`, ...), or an expression whose value is dropped. -/
def exprStmt (env : Env) (t : Json) (k : Env → S LExpr) : S LExpr := do
  -- `x = v op e`, with the check of `op` (`remChecked` for `%`)
  let update (x : String) (op : BinOp) (e : LExpr) : LExpr :=
    let v : LExpr := ⟨.var x, .leaf (span t)⟩
    if op == .mod then remChecked t v e
    else checked t op (node t (.binop op v.expr e.expr) [v, e])
  match kind t, str t "opcode", inner t with
  | "BinaryOperator", some "=", [l, r] =>
    let some x := local? env l | unsupported l "an assignment to this"
    return letin t x (← expr env r) (← k env)
  | "CompoundAssignOperator", some op, [l, r] =>
    let some x := local? env l | unsupported l "an assignment to this"
    let some o := arith (String.ofList (op.toList.dropLast)) | unsupported t s!"the operator `{op}`"
    return letin t x (update x o (← expr env r)) (← k env)
  | "UnaryOperator", some op, [l] =>
    if op == "++" || op == "--" then
      let some x := local? env l | unsupported l "an assignment to this"
      let o := if op == "++" then BinOp.add else .sub
      return letin t x (update x o (int t 1)) (← k env)
    else return letin t "_" (← expr env t) (← k env)
  | _, _, _ => return letin t "_" (← expr env t) (← k env)

/-- The locals declared by `ds` (`int x = e, y;`), then `k`. A local without a value is
    `0`: reading it is undefined behaviour in C (not reported yet). -/
def decls (env : Env) (ds : List Json) (k : Env → S LExpr) : S LExpr := do
  match ds with
  | [] => k env
  | d :: ds =>
    unless kind d == "VarDecl" do unsupported d "this declaration"
    unless qualType d == "int" do unsupported d s!"the type `{qualType d}`"
    let some id := str d "id" | unsupported d "a declaration without an id"
    let some x := str d "name" | unsupported d "a declaration without a name"
    let e ← match inner d with
      | [e] => expr env e
      | _ => pure (int d 0)
    let y ← fresh x
    return letin d y e (← decls ((id, y) :: env) ds k)

mutual

/-- The statement `s`, then `k` with the names in scope after `s`. -/
partial def stmt (env : Env) (s : Json) (k : Env → S LExpr) : S LExpr := do
  match kind s, inner s with
  -- the locals of a block are only in scope in the block
  | "CompoundStmt", ss => stmts env ss fun _ => k env
  | "DeclStmt", ds => decls env ds k
  | "ReturnStmt", [e] => expr env e
  | "NullStmt", _ => k env
  | k', _ =>
    if k'.endsWith "Stmt" then unsupported s s!"this statement ({k'})"
    else exprStmt env s k

/-- The statements `ss`, one after the other, then `k`. -/
partial def stmts (env : Env) (ss : List Json) (k : Env → S LExpr) : S LExpr :=
  match ss with
  | [] => k env
  | s :: ss => stmt env s fun env => stmts env ss k

end

/-- The body `t` of the function `f`. If it ends without `return`, `main` gives `0`, as
    in C, and the other functions `()`: their result is undefined in C, and `()` makes
    any use of it an error. `names` are the names of the parameters. -/
def body (f : String) (env : Env) (names : List String) (t : Json) : M LExpr :=
  let fallOff : LExpr := if f == "main" then int t 0 else ⟨.unit, .leaf (span t)⟩
  (stmt env t fun _ => pure fallOff).run' names

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
  let b ← body f env (env.map (·.2)) b
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
