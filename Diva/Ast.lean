namespace Diva

/-- Binary operators. -/
inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq, Inhabited

def ppBinOp : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "mod"
  | .eq  => "="
  | .ne  => "<>"
  | .lt  => "<"
  | .le  => "<="
  | .gt  => ">"
  | .ge  => ">="

/-- AST for the currently supported language:
```
e ::= n                                    -- natural number literal
    | true | false                         -- boolean literals
    | ()                                   -- unit literal
    | x                                    -- variable
    | e e                                  -- application (left-associative)
    | fun x -> e                           -- lambda
    | let x = e in e                       -- let binding
    | let [rec] f x = e in e               -- [recursive] function
    | if e then e else e                   -- conditional
    | e op e                               -- binary operator
    | [] | e :: e                          -- lists
    | match e with [] -> e | x :: xs -> e  -- list case match analysis
    | assert e                             -- runtime check
```
-/
inductive Expr where
  | int   : Int → Expr
  | bool  : Bool → Expr
  | unit  : Expr
  | var   : String → Expr
  | app   : Expr → Expr → Expr
  | lam   : String → Expr → Expr
  | letin : String → Expr → Expr → Expr
  | letrec : String → String → Expr → Expr → Expr
    -- `let rec f x = e1 in e2`
  | ite   : Expr → Expr → Expr → Expr
  | binop : BinOp → Expr → Expr → Expr
  | nil   : Expr
  | cons  : Expr → Expr → Expr
  | matchList : Expr → Expr → String → String → Expr → Expr
    -- `match e1 with [] -> e2 | s1 :: s2 -> e3`
  | assert : Expr → Expr
  deriving Inhabited

def ppExpr : Expr → String
  | .int n         => toString n
  | .bool b        => toString b
  | .unit          => "()"
  | .var x         => x
  | .binop op a b  => s!"({ppExpr a} {ppBinOp op} {ppExpr b})"
  | .app f a       => s!"({ppExpr f} {ppExpr a})"
  | .lam x body    => s!"(fun {x} -> {ppExpr body})"
  | .letin x e1 e2 => s!"(let {x} = {ppExpr e1} in {ppExpr e2})"
  | .letrec f x e1 e2 => s!"(let rec {f} {x} = {ppExpr e1} in {ppExpr e2})"
  | .ite c t e     => s!"(if {ppExpr c} then {ppExpr t} else {ppExpr e})"
  | .nil           => "[]"
  | .cons a b      => s!"({ppExpr a} :: {ppExpr b})"
  | .matchList s n x xs c =>
    s!"(match {ppExpr s} with [] -> {ppExpr n} | {x} :: {xs} -> {ppExpr c})"
  | .assert c      => s!"(assert {ppExpr c})"

instance : Repr Expr := ⟨fun e _ => Std.Format.text (ppExpr e)⟩

instance : ToString Expr := ⟨ppExpr⟩

end Diva
