import Diva.AbsInt.Infer

/-!
# Diagnostics (untrusted)

Says where a program may fail, and why. `diagnose` follows `mayFail`: the same
abstract environments, and only the branches that can be taken. At each place where
one of `mayFail`'s local checks fails, it gives a message with the code.

Nothing here is proved. The verified answer is `mayFail` (see `safe`).

This is separate from `mayFail` so that the checker stays small: `mayFail` is proved
and run by the kernel (`decide`), and messages would add strings and printing to
both. If `mayFail` says the program may fail but `diagnose` finds nothing, `report`
still says "may fail".

TODO: in the future, find a way to merge the two in a clean way
-/

namespace Diva.Report

open AbsInt AbsDomain NumDomain

variable {A : Type} [NumDomain A] [ToString A]

/-- `s` without the `#n` suffixes that `resolve` adds to names. -/
def clean (s : String) : String :=
  match s.splitOn "#" with
  | [] => ""
  | p :: ps => p ++ String.join (ps.map fun q => String.ofList (q.toList.dropWhile Char.isDigit))

/-- `e`, short, in backquotes. -/
def snippet (e : Expr) : String :=
  let s := clean (ppExpr e)
  if s.length ≤ 60 then s!"`{s}`" else s!"`{s.take 57}...`"

/-- Why a call of `af` on `aa` may fail (when `callMayFail` says so). -/
def callReason (af aa : AVal A) : String :=
  match af.sum with
  | none =>
    if af.within Flat.fnV then "calls a function the analysis knows nothing about"
    else s!"may call something that is not a function ({af})"
  | some S =>
    if !af.toFlat.leq Flat.bot || af.elems.isSome then
      s!"may call something that is not a function ({af})"
    else if !aa.flat.leq S.pre then
      s!"the argument ({aa}) is not in the precondition ({S.pre})"
    else "the function called may fail"

/-- Why `op` may fail on `a` and `b` (when `opMayFail` says so). -/
def opReason (op : BinOp) (a b : AVal A) : String :=
  match op with
  | .eq | .ne => s!"the operands may not be two integers or two booleans ({a} and {b})"
  | .div | .mod =>
    let ints := a.within Flat.ints && b.within Flat.ints
    let zero := (cmpEq b.int (const 0)).1
    ", ".intercalate
      ((if ints then [] else [s!"the operands may not be integers ({a} and {b})"]) ++
       (if zero then [s!"possible division by zero (divisor: {b})"] else []))
  | _ => s!"the operands may not be integers ({a} and {b})"

/-- The messages for `e`, analysed in `σ` with the hints `H`. -/
def diagnose (H : Hints A) (σ : AEnv A) : Expr → List String
  | .int _ | .bool _ | .unit | .nil => []
  | .var x => if (σ.lookup x).isNone then [s!"`{clean x}` may be unbound"] else []
  | e@(.binop op a b) =>
    let va := aeval H σ a
    let vb := aeval H σ b
    diagnose H σ a ++ diagnose H σ b ++
      (if opMayFail op va vb then [s!"{snippet e}: {opReason op va vb}"] else [])
  | e@(.cons a b) =>
    let vb := aeval H σ b
    diagnose H σ a ++ diagnose H σ b ++
      (if vb.within Flat.listV then [] else [s!"{snippet e}: the tail may not be a list ({vb})"])
  | .letin x e1 e2 => diagnose H σ e1 ++ diagnose H ((x, aeval H σ e1) :: σ) e2
  | .lam x b => diagnose H ((x, AVal.ofFlat (H.param x)) :: σ) b
  | e@(.app f a) =>
    let vf := aeval H σ f
    let va := aeval H σ a
    diagnose H σ f ++ diagnose H σ a ++
      (if callMayFail vf va then [s!"{snippet e}: {callReason vf va}"] else [])
  | .letrec f x b e2 =>
    -- the body, assuming that the recursive calls don't fail (as in `mayFail`)
    let P := H.param x
    let S : Summary A := ⟨P, restPres H b, H.result f, false⟩
    let vf := letrecVal H σ f x b
    let rejected :=
      if vf.sum.isNone then
        [s!"`{clean f}`: the result of its body is not in the claimed result \
          ({H.result f}), so its calls are unknown"]
      else []
    diagnose H ((x, AVal.ofFlat P) :: (f, AVal.summary S) :: σ) b ++ rejected ++
      diagnose H ((f, vf) :: σ) e2
  | .ite c t e =>
    let vc := aeval H σ c
    diagnose H σ c ++
      (if vc.within Flat.anyBool then [] else [s!"{snippet c} may not be a boolean ({vc})"]) ++
      (if vc.tt then ((σ.assume c true).map (diagnose H · t)).getD [] else []) ++
      (if vc.ff then ((σ.assume c false).map (diagnose H · e)).getD [] else [])
  | e@(.assert c) =>
    let vc := aeval H σ c
    diagnose H σ c ++
      (if !vc.within Flat.anyBool then [s!"{snippet e}: the condition may not be a boolean ({vc})"]
       else if vc.ff then [s!"{snippet e} may fail"]
       else [])
  | e@(.matchList s n x xs c) =>
    let vs := aeval H σ s
    diagnose H σ s ++
      (if vs.within Flat.listV then [] else [s!"{snippet e}: may not match a list ({vs})"]) ++
      (if vs.mayBeNil then diagnose H σ n else []) ++
      (if vs.heads.leq Flat.bot then []
       else diagnose H ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c)
  | .exn _ a => diagnose H σ a
  -- `raise`, `try`, arrays and refs (`mayFail` says `true`)
  | e => [s!"{snippet e}: not analysed yet, so it may fail"]

/-- The report for a program `e` whose free variables `σ` describes, with inferred
    hints. -/
def report (σ : AEnv A) (e : Expr) : List String :=
  let H := inferHints σ e
  if mayFail H σ e then
    match diagnose H σ e with
    | [] => ["may fail"]   -- not expected: `diagnose` follows `mayFail`
    | ds => ds
  else ["no runtime error is possible"]

end Diva.Report
