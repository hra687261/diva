import Diva.AbsInt.Infer
import Diva.Loc
import Diva.Overflow

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

/-- The messages for `e`, analysed in `σ` with the hints `H`. `l` has the positions of
    `e`, and `place` prints a span (`""` for none). -/
def diagnose (H : Hints A) (place : Span → String) : AEnv A → Expr → Loc → List String
  | _, .int _, _ | _, .bool _, _ | _, .unit, _ | _, .nil, _ => []
  | σ, .var x, l => if (σ.lookup x).isNone then [msg l s!"`{clean x}` may be unbound"] else []
  | σ, e@(.binop op a b), l =>
    let va := aeval H σ a
    let vb := aeval H σ b
    diagnose H place σ a (l.kid 0) ++ diagnose H place σ b (l.kid 1) ++
      (if opMayFail op va vb then [msg l s!"{snippet e}: {opReason op va vb}"] else [])
  | σ, e@(.cons a b), l =>
    let vb := aeval H σ b
    diagnose H place σ a (l.kid 0) ++ diagnose H place σ b (l.kid 1) ++
      (if vb.within Flat.listV then []
       else [msg l s!"{snippet e}: the tail may not be a list ({vb})"])
  | σ, e@(.letin x e1 e2), l =>
    let v1 := aeval H σ e1
    match Overflow.bits? e with
    -- a check that `Overflow.check` adds: its message is about the operation `e1`
    | some bits =>
      diagnose H place σ e1 (l.kid 0) ++
        (if mayFail H ((x, v1) :: σ) e2 then
           [msg l s!"{snippet e1}: may overflow {bits}-bit integers (result: {v1})"]
         else [])
    | none => diagnose H place σ e1 (l.kid 0) ++ diagnose H place ((x, v1) :: σ) e2 (l.kid 1)
  | σ, .lam x b, l => diagnose H place ((x, AVal.ofFlat (H.param x)) :: σ) b (l.kid 0)
  | σ, e@(.app f a), l =>
    let vf := aeval H σ f
    let va := aeval H σ a
    diagnose H place σ f (l.kid 0) ++ diagnose H place σ a (l.kid 1) ++
      (if callMayFail vf va then [msg l s!"{snippet e}: {callReason vf va}"] else [])
  | σ, .letrec f x b e2, l =>
    -- the body, assuming that the recursive calls don't fail (as in `mayFail`)
    let P := H.param x
    let S : Summary A := ⟨P, restPres H b, H.result f, false⟩
    let vf := letrecVal H σ f x b
    let rejected :=
      if vf.sum.isNone then
        [msg l s!"`{clean f}`: the result of its body is not in the claimed result \
          ({H.result f}), so its calls are unknown"]
      else []
    diagnose H place ((x, AVal.ofFlat P) :: (f, AVal.summary S) :: σ) b (l.kid 0) ++ rejected ++
      diagnose H place ((f, vf) :: σ) e2 (l.kid 1)
  | σ, .ite c t e, l =>
    let vc := aeval H σ c
    diagnose H place σ c (l.kid 0) ++
      (if vc.within Flat.anyBool then []
       else [msg (l.kid 0) s!"{snippet c} may not be a boolean ({vc})"]) ++
      (if vc.tt then ((σ.assume c true).map (diagnose H place · t (l.kid 1))).getD [] else []) ++
      (if vc.ff then ((σ.assume c false).map (diagnose H place · e (l.kid 2))).getD [] else [])
  | σ, e@(.assert c), l =>
    let vc := aeval H σ c
    diagnose H place σ c (l.kid 0) ++
      (if !vc.within Flat.anyBool then
         [msg l s!"{snippet e}: the condition may not be a boolean ({vc})"]
       else if vc.ff then [msg l s!"{snippet e} may fail"]
       else [])
  | σ, e@(.matchList s n x xs c), l =>
    let vs := aeval H σ s
    diagnose H place σ s (l.kid 0) ++
      (if vs.within Flat.listV then [] else [msg l s!"{snippet e}: may not match a list ({vs})"]) ++
      (if vs.mayBeNil then diagnose H place σ n (l.kid 1) else []) ++
      (if vs.heads.leq Flat.bot then []
       else diagnose H place ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c (l.kid 2))
  | σ, .exn _ a, l => diagnose H place σ a (l.kid 0)
  -- `raise`, `try`, arrays and refs (`mayFail` says `true`)
  | _, e, l => [msg l s!"{snippet e}: not analysed yet, so it may fail"]
where
  /-- `m`, after the position of `l` if `place` prints one. -/
  msg (l : Loc) (m : String) : String :=
    let p := place l.span
    if p.isEmpty then m else s!"{p}: {m}"

/-- What `diva check` prints for the program `e`: where `e` may fail, or that it
    can't fail. `σ` gives the values of the variables that `e` uses without
    defining them (`[]` for a complete program). `inferHints` infers the hints, but
    uses the hints of `fixed` unchanged. The report still checks the hints of
    `fixed`. `l` has the positions of `e`, and `place` prints a span (`""` for none). -/
def report (σ : AEnv A) (e : Expr) (fixed : Hints A := []) (l : Loc := default)
    (place : Span → String := fun _ => "") : List String :=
  let H := inferHints σ e fixed
  if mayFail H σ e then
    match diagnose H place σ e l with
    | [] => ["may fail"]   -- not expected: `diagnose` follows `mayFail`
    | ds => ds
  else ["no runtime error is possible"]

end Diva.Report
