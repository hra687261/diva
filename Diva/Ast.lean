namespace Diva

/-- Binary operators. -/
inductive BinOp where
  | add | sub | mul | eq | lt
  deriving Repr, DecidableEq, Inhabited

def ppBinOp : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eq  => "="
  | .lt  => "<"

/-- AST for the currently supported language:
```
e ::= n                      -- natural number literal
    | true | false           -- booleans
    | x                      -- variable
    | e e                    -- application (left-associative)
    | fun x -> e             -- lambda
    | let x = e in e         -- let binding (non-recursive)
    | if e then e else e     -- conditional
    | e + e | e - e | e * e  -- arithmetic
    | e = e | e < e          -- comparisons (produce booleans)
```
-/
inductive Expr where
  | int   : Int → Expr
  | bool  : Bool → Expr
  | var   : String → Expr
  | app   : Expr → Expr → Expr
  | lam   : String → Expr → Expr
  | letin : String → Expr → Expr → Expr
  | ite   : Expr → Expr → Expr → Expr
  | binop : BinOp → Expr → Expr → Expr
  deriving Inhabited

def ppExpr : Expr → String
  | .int n         => toString n
  | .bool b        => toString b
  | .var x         => x
  | .binop op a b  => s!"({ppExpr a} {ppBinOp op} {ppExpr b})"
  | .app f a       => s!"({ppExpr f} {ppExpr a})"
  | .lam x body    => s!"(fun {x} -> {ppExpr body})"
  | .letin x e1 e2 => s!"(let {x} = {ppExpr e1} in {ppExpr e2})"
  | .ite c t e     => s!"(if {ppExpr c} then {ppExpr t} else {ppExpr e})"

instance : Repr Expr := ⟨fun e _ => Std.Format.text (ppExpr e)⟩

instance : ToString Expr := ⟨ppExpr⟩

end Diva
