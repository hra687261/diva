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

/-- `op` is a comparison: its result is a boolean. -/
def BinOp.isCmp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- AST for the currently supported language (`doc/grammar.md` has the whole grammar,
    and says which commands support each rule):
```
e ::= n                                      -- natural number literal
    | true | false                           -- boolean literals
    | ()                                     -- unit literal
    | x                                      -- variable
    | e e                                    -- application (left-associative)
    | fun x -> e                             -- lambda
    | let x = e in e                         -- let binding
    | let [rec] f x = e in e                 -- [recursive] function
    | if e then e else e                     -- conditional
    | e op e                                 -- binary operator
    | [] | e :: e                            -- lists
    | match e with [] -> e | x :: xs -> e    -- list case match analysis
    | assert e                               -- runtime check
    | Array.make e e                         -- new array: length, initial value
    | e.(e) | e.(e) <- e                     -- array read and write
    | Array.length e                         -- array length
    | ref e | !e | e := e                    -- refs
    | for x = e to e do e done               -- loops, desugared to recursion
    | while e do e done
    | E | E e | raise e                      -- exceptions
    | try e with E x -> e | F -> e | k -> e  -- catch exceptions
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
  | alloc : Nat → Expr → Expr → Expr
    -- `Array.make n v`, the Nat is the id of the allocation site
  | get   : Expr → Expr → Expr          -- `a.(i)`
  | set   : Expr → Expr → Expr → Expr   -- `a.(i) <- v`
  | len   : Expr → Expr                 -- `Array.length a`
  | ref   : Nat → Expr → Expr
    -- `ref v`, the Nat is the id of the allocation site
  | deref : Expr → Expr                 -- `!r`
  | assign : Expr → Expr → Expr         -- `r := v`
  | ctor  : String → Expr → Expr        -- `C v`: the constructor `C` applied to `v`
  | raise : Expr → Expr                 -- `raise e`
  | tryw  : Expr → String → Expr → Expr
    -- `try e with k -> h`: catch any exception as `k`
  | ctorCase : Expr → String → String → Expr → Expr → Expr
    -- `match e1 with C x -> e2 | _ -> e3`: test the constructor of `e1`
  deriving Inhabited, BEq, DecidableEq

/-- `e` contains no call and doesn't have side effects on the store (no `Array.make`,
    `<-`, `ref` or `:=`). Such expressions can be optimized and replaced by their
    value. As in Lean, a pure expression may still fail (`1 / 0`, `assert`,
    `raise`). `mayFail` checks that separately. -/
def Expr.pure : Expr → Bool
  | .int _ | .bool _ | .unit | .var _ | .nil | .lam _ _ => true
  | .app _ _ | .alloc .. | .set .. | .ref .. | .assign .. => false
  | .letin _ a b | .binop _ a b | .cons a b | .get a b | .tryw a _ b => a.pure && b.pure
  | .letrec _ _ _ b | .assert b | .len b | .deref b | .ctor _ b | .raise b => b.pure
  | .ite c t e | .matchList c t _ _ e | .ctorCase c _ _ t e => c.pure && t.pure && e.pure

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
  | .alloc _ n v   => s!"(Array.make {ppExpr n} {ppExpr v})"
  | .get a i       => s!"{ppExpr a}.({ppExpr i})"
  | .set a i v     => s!"({ppExpr a}.({ppExpr i}) <- {ppExpr v})"
  | .len a         => s!"(Array.length {ppExpr a})"
  | .ref _ v       => s!"(ref {ppExpr v})"
  | .deref r       => s!"!{ppExpr r}"
  | .assign r v    => s!"({ppExpr r} := {ppExpr v})"
  | .ctor c .unit   => c
  | .ctor c v       => s!"({c} {ppExpr v})"
  | .raise e       => s!"(raise {ppExpr e})"
  | .tryw e k h     => s!"(try {ppExpr e} with {k} -> {ppExpr h})"
  | .ctorCase s c x h m =>
    s!"(match {ppExpr s} with {c} {x} -> {ppExpr h} | _ -> {ppExpr m})"

instance : Repr Expr := ⟨fun e _ => Std.Format.text (ppExpr e)⟩

instance : ToString Expr := ⟨ppExpr⟩

/-- `fun x₁ -> ... -> fun xₙ -> body`, for the parameters `xs = [x₁, ..., xₙ]`. So
    `fun x y -> e` is `fun x -> fun y -> e`. -/
@[simp] def lams : List String → Expr → Expr
  | [], body => body
  | x :: xs, body => .lam x (lams xs body)

/-- A term of a contract: integers, booleans, names, `+`, `-`, `*`, comparisons, `&&`,
    `||`, `not`, and `length l` for a list `l`. Contracts use a small part of Gospel, the
    specification language for OCaml: https://ocaml-gospel.github.io/gospel/ -/
inductive Term where
  | int : Int → Term
  | bool : Bool → Term
  | var : String → Term
  | binop : BinOp → Term → Term → Term
  | and : Term → Term → Term
  | or : Term → Term → Term
  | not : Term → Term
  /-- `length l`: the number of elements of the list `l`. -/
  | length : Term → Term
  deriving Inhabited, Repr, BEq

/-- The names used in `t`. -/
def Term.vars : Term → List String
  | .int _ | .bool _ => []
  | .var x => [x]
  | .binop _ a b | .and a b | .or a b => a.vars ++ b.vars
  | .not a | .length a => a.vars

/-- The kind of a name of a contract: an integer, a boolean or a list. -/
inductive Kind where
  | int | bool | list
  deriving Inhabited, Repr, BEq

/-- The kind of the value of `t`, if `t` shows it: a name doesn't. -/
def Term.kind? : Term → Option Kind
  | .int _ | .length _ => some .int
  | .bool _ | .and .. | .or .. | .not _ => some .bool
  | .binop op _ _ => some (if op.isCmp then .bool else .int)
  | .var _ => none

/-- The kinds that `t` gives to its names, if `t` is of the kind `k`: `length x` makes
    `x` a list, `not x` and `x || y` make `x` a boolean, and in `x = t`, `x` has the
    kind of `t`. -/
def Term.kindsAt (k : Kind) : Term → List (String × Kind)
  | .int _ | .bool _ => []
  | .var x => [(x, k)]
  | .and a b | .or a b => a.kindsAt .bool ++ b.kindsAt .bool
  | .not a => a.kindsAt .bool
  | .length a => a.kindsAt .list
  | .binop op a b =>
    if op == .eq || op == .ne then
      match a.kind? <|> b.kind? with
      | some k => a.kindsAt k ++ b.kindsAt k
      | none => []
    else a.kindsAt .int ++ b.kindsAt .int

/-- The kind of the name `x` in the clauses `ts` (each one is a boolean): a list or a
    boolean if a clause makes it one, else an integer. -/
def kindOf (ts : List Term) (x : String) : Kind :=
  let ks := (ts.flatMap (·.kindsAt .bool)).filterMap fun (y, k) => if y == x then some k else none
  if ks.contains .list then .list else if ks.contains .bool then .bool else .int

/-- The contract of a function, written in a Gospel comment after it:
    `(*@ r = f x requires ... ensures ... *)`. -/
structure Spec where
  /-- The name of the result in `ensures`: `r` in the header `r = f x`, `result`
      without a header. -/
  result : String := "result"
  /-- The name of the function in the header, if there is one. -/
  name : Option String := none
  /-- The names of the parameters in the header. -/
  params : List String := []
  requires : List Term := []
  ensures : List Term := []
  deriving Inhabited, Repr, BEq

/-- A declaration `let f ... = e` or `let rec f x ... = e`, without what follows
    it. -/
inductive Binding where
  /-- `let f = e`. For `let f x y = e`, `e` is `fun x y -> e`. -/
  | val : String → Expr → Binding
  /-- `let rec f x = e`. For `let rec f x y = e`, `e` is `fun y -> e`. -/
  | recFn : String → String → Expr → Binding
  deriving BEq

/-- The name the declaration defines. -/
def Binding.name : Binding → String
  | .val f _ | .recFn f _ _ => f

/-- The declaration, followed by `e`. -/
def Binding.bind : Binding → Expr → Expr
  | .val f a, e => .letin f a e
  | .recFn f x a, e => .letrec f x a e

/-- A top-level item: a declaration `let f x = e` (without `in`), with the contract
    that follows it if there is one, or an expression. -/
inductive Item where
  | decl : Binding → Option Spec → Item
  | expr : Expr → Item
  deriving BEq

/-- The free names of `e`: the names that `e` uses, minus the names in `bound` and the
    names that `e` binds. A name is bound by `fun`, `let`, `let rec`,
    `match ... with x :: xs`, `try ... with k` and `E x`. `bound` are the names
    bound by the expressions "above" `e`: in `fun y -> e`, `y` is in `bound`
    for `e`. -/
def freeNames (bound : List String) : Expr → List String
  | .int _ | .bool _ | .unit | .nil => []
  | .var x => if bound.contains x then [] else [x]
  | .lam x b => freeNames (x :: bound) b
  | .letin x a b => freeNames bound a ++ freeNames (x :: bound) b
  | .letrec f x a b => freeNames (f :: x :: bound) a ++ freeNames (f :: bound) b
  | .matchList s n x xs c =>
    freeNames bound s ++ freeNames bound n ++ freeNames (x :: xs :: bound) c
  | .tryw a k h => freeNames bound a ++ freeNames (k :: bound) h
  | .ctorCase s _ x h m =>
    freeNames bound s ++ freeNames (x :: bound) h ++ freeNames bound m
  | .assert b | .len b | .ref _ b | .deref b | .ctor _ b | .raise b => freeNames bound b
  | .app a b | .binop _ a b | .cons a b | .get a b | .assign a b | .alloc _ a b =>
    freeNames bound a ++ freeNames bound b
  | .ite a b c | .set a b c => freeNames bound a ++ freeNames bound b ++ freeNames bound c

/-- A name bound "above" `e` is not free in `e`: removing `x` from `bound` adds only
    `x` to the free names. -/
theorem mem_freeNames_cons {y x : String} (e : Expr) :
    ∀ bound : List String, y ∈ freeNames (x :: bound) e ↔ y ≠ x ∧ y ∈ freeNames bound e := by
  induction e generalizing x with
  | var z =>
    intro bound
    simp only [freeNames, List.contains_cons]
    grind
  | _ =>
    intro bound
    simp only [freeNames, List.mem_append]
    -- `simp` already proves the cases with a single sub-expression
    try grind

end Diva
