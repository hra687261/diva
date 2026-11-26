import Diva.AbsInt.Infer
import Diva.Loc
import Diva.Overflow

/-!
# Diagnostics (untrusted)

Says where a program may fail, and why. `diagnose` follows `mayFailStore`, the analysis
with arrays and refs: the same abstract environments, and only the branches that can
be taken. At each place where one of its local checks fails, it gives a message with
the code. `mayFailStore` is `mayFail` with the store analysed. Without arrays and refs,
the two are the same.

Nothing here is proved. The verified answer is `mayFail` (see `safe`). `mayFailStore`
isn't proved yet.

This is separate from `mayFail` so that the checker stays small: `mayFail` is proved
and run by the kernel (`decide`), and messages would add strings and printing to
both. If `mayFailStore` says the program may fail but `diagnose` finds nothing, `report`
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

/-- The code that a message is about, in backquotes, cut to 60 characters. It is the
    text of the file at the span of `l`, as the user wrote it (`code` gives it). If the
    file has no text there, for example for a check that DIVA added, it is the
    expression `e`, printed. -/
def snippet (code : Span → String) (e : Expr) (l : Loc) : String :=
  let s := match code l.span with
    | "" => clean (ppExpr e)
    | s => s
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
    `e`, `place` prints a span (`""` for none), and `code` gives the source text of a
    span (`""` for none). -/
def diagnose (H : Hints A) (place code : Span → String) :
    AEnv A → Expr → Loc → List String
  | _, .int _, _ | _, .bool _, _ | _, .unit, _ | _, .nil, _ => []
  | σ, .var x, l => if (σ.lookup x).isNone then [msg l s!"`{clean x}` may be unbound"] else []
  | σ, e@(.binop op a b), l =>
    let va := aevalStore H σ a
    let vb := aevalStore H σ b
    diagnose H place code σ a (l.kid 0) ++ diagnose H place code σ b (l.kid 1) ++
      (if opMayFail op va vb then [msg l s!"{snippet code e l}: {opReason op va vb}"] else [])
  | σ, e@(.cons a b), l =>
    let vb := aevalStore H σ b
    diagnose H place code σ a (l.kid 0) ++ diagnose H place code σ b (l.kid 1) ++
      (if vb.within Flat.listV then []
       else [msg l s!"{snippet code e l}: the tail may not be a list ({vb})"])
  | σ, e@(.letin x e1 e2), l =>
    let v1 := aevalStore H σ e1
    match Overflow.bits? e with
    -- a check that `Overflow.check` adds: its message is about the operation `e1`
    | some bits =>
      diagnose H place code σ e1 (l.kid 0) ++
        (if mayFailStore H ((x, v1) :: σ) e2 then
           [msg l s!"{snippet code e1 (l.kid 0)}: may overflow {bits}-bit integers (result: {v1})"]
         else [])
    | none =>
      diagnose H place code σ e1 (l.kid 0) ++ diagnose H place code ((x, v1) :: σ) e2 (l.kid 1)
  | σ, .lam x b, l => diagnose H place code ((x, AVal.ofFlat (H.param x)) :: σ) b (l.kid 0)
  | σ, e@(.app f a), l =>
    let vf := aevalStore H σ f
    let va := aevalStore H σ a
    diagnose H place code σ f (l.kid 0) ++ diagnose H place code σ a (l.kid 1) ++
      (if callMayFail vf va then [msg l s!"{snippet code e l}: {callReason vf va}"] else [])
  | σ, .letrec f x b e2, l =>
    -- the body, assuming that the recursive calls don't fail (as in `mayFail`)
    let P := H.param x
    let S : Summary A := ⟨P, restPres H b, H.result f, false⟩
    let vf := aevalStore H σ (.letrec f x b (.var f))
    let rejected :=
      if vf.sum.isNone then
        [msg l s!"`{clean f}`: the result of its body is not in the claimed result \
          ({H.result f}), so its calls are unknown"]
      else []
    diagnose H place code ((x, AVal.ofFlat P) :: (f, AVal.summary S) :: σ) b (l.kid 0) ++ rejected ++
      diagnose H place code ((f, vf) :: σ) e2 (l.kid 1)
  | σ, .ite c t e, l =>
    let vc := aevalStore H σ c
    diagnose H place code σ c (l.kid 0) ++
      (if vc.within Flat.anyBool then []
       else [msg (l.kid 0) s!"{snippet code c (l.kid 0)} may not be a boolean ({vc})"]) ++
      (if vc.tt then ((σ.assume c true).map (diagnose H place code · t (l.kid 1))).getD [] else []) ++
      (if vc.ff then ((σ.assume c false).map (diagnose H place code · e (l.kid 2))).getD [] else [])
  | σ, e@(.assert c), l =>
    let vc := aevalStore H σ c
    diagnose H place code σ c (l.kid 0) ++
      (if !vc.within Flat.anyBool then
         [msg l s!"{snippet code e l}: the condition may not be a boolean ({vc})"]
       else if vc.ff then [msg l s!"{snippet code e l} may fail"]
       else [])
  | σ, e@(.matchList s n x xs c), l =>
    let vs := aevalStore H σ s
    diagnose H place code σ s (l.kid 0) ++
      (if vs.within Flat.listV then [] else [msg l s!"{snippet code e l}: may not match a list ({vs})"]) ++
      (if vs.mayBeNil then diagnose H place code σ n (l.kid 1) else []) ++
      (if vs.heads.leq Flat.bot then []
       else diagnose H place code ((xs, vs.tails) :: (x, AVal.ofFlat vs.heads) :: σ) c (l.kid 2))
  | σ, .exn _ a, l => diagnose H place code σ a (l.kid 0)
  -- the store (as in `mayFailStore`)
  | σ, e@(.ref site v), l =>
    diagnose H place code σ v (l.kid 0) ++ writeMsgs l e [site] (aevalStore H σ v)
  | σ, e@(.deref r), l =>
    let ar := aevalStore H σ r
    diagnose H place code σ r (l.kid 0) ++
      (if ar.refsOnly then [] else [msg l s!"{snippet code e l}: may not be a ref ({ar})"])
  | σ, e@(.assign r v), l =>
    let ar := aevalStore H σ r
    diagnose H place code σ r (l.kid 0) ++ diagnose H place code σ v (l.kid 1) ++
      (if ar.refsOnly then writeMsgs l e ar.refs (aevalStore H σ v)
       else [msg l s!"{snippet code e l}: may not be a ref ({ar})"])
  | σ, e@(.alloc site n v), l =>
    let an := aevalStore H σ n
    diagnose H place code σ n (l.kid 0) ++ diagnose H place code σ v (l.kid 1) ++
      (if !an.within Flat.ints then
         [msg l s!"{snippet code e l}: the length may not be an integer ({an})"]
       else if (cmpLe (const 0) an.int).2 then
         [msg l s!"{snippet code e l}: the length may be negative ({an})"]
       else if !an.flat.leq (H.len site) then
         [msg l s!"{snippet code e l}: the length ({an}) is not in the hint `!{site}.length` \
           ({H.len site})"]
       else []) ++
      writeMsgs l e [site] (aevalStore H σ v)
  | σ, e@(.get a i), l =>
    diagnose H place code σ a (l.kid 0) ++ diagnose H place code σ i (l.kid 1) ++
      accessMsgs l e (aevalStore H σ a) (aevalStore H σ i)
  | σ, e@(.set a i v), l =>
    let aa := aevalStore H σ a
    diagnose H place code σ a (l.kid 0) ++ diagnose H place code σ i (l.kid 1) ++
      diagnose H place code σ v (l.kid 2) ++
      (match accessMsgs l e aa (aevalStore H σ i) with
       | [] => writeMsgs l e aa.arrs (aevalStore H σ v)
       | ms => ms)
  | σ, e@(.len a), l =>
    let aa := aevalStore H σ a
    diagnose H place code σ a (l.kid 0) ++
      (if aa.arrsOnly then [] else [msg l s!"{snippet code e l}: may not be an array ({aa})"])
  -- `raise` and `try` (`mayFailStore` says `true`)
  | _, e, l => [msg l s!"{snippet code e l}: not analysed yet, so it may fail"]
where
  /-- `m`, after the position of `l` if `place` prints one. -/
  msg (l : Loc) (m : String) : String :=
    let p := place l.span
    if p.isEmpty then m else s!"{p}: {m}"
  /-- The messages of the write `e` of `v` to the sites `ss`: for each site whose
      hint `!s` doesn't contain `v`. -/
  writeMsgs (l : Loc) (e : Expr) (ss : List Nat) (v : AVal A) : List String :=
    ss.filterMap fun s =>
      if v.flat.leq (H.cell s) then none
      else some (msg l s!"{snippet code e l}: the value written ({v}) is not in the hint \
        `!{s}` ({H.cell s})")
  /-- The messages of the access `e` to the array `a` at the index `i`. -/
  accessMsgs (l : Loc) (e : Expr) (a i : AVal A) : List String :=
    if !a.arrsOnly then [msg l s!"{snippet code e l}: may not be an array ({a})"]
    else if inBounds H a i then []
    else [msg l s!"{snippet code e l}: the index ({i}) may be out of bounds (length: \
      {Hints.joinAt H.len a.arrs})"]

/-- What `diva check` says when the program can't fail, but only the analysis of the
    store, which isn't proved yet, shows it. -/
def unprovedSafe : String :=
  "no runtime error found, but not proved: the analysis of arrays and refs isn't proved yet"

/-- What `diva check` prints for the program `e`: where `e` may fail, or that it
    can't fail. `σ` gives the values of the variables that `e` uses without
    defining them (`[]` for a complete program). `inferHints` infers the hints, but
    uses the hints of `fixed` unchanged. The report still checks the hints of
    `fixed`. `l` has the positions of `e`, `place` prints a span (`""` for none), and
    `code` gives the source text of a span (`""` for none).

    If the checker (`mayFail`) proves that `e` can't fail, the report says so.
    Otherwise it follows the analysis with arrays and refs (`mayFailStore`), which isn't
    proved yet: the places where it says `e` may fail, or `unprovedSafe`. -/
def report (σ : AEnv A) (e : Expr) (fixed : Hints A := []) (l : Loc := default)
    (place : Span → String := fun _ => "") (code : Span → String := fun _ => "") :
    List String :=
  let H := inferHints σ e fixed
  if !mayFail H σ e then ["no runtime error is possible"]
  else if mayFailStore H σ e then
    match diagnose H place code σ e l with
    | [] => ["may fail"]   -- not expected: `diagnose` follows `mayFailStore`
    | ds => ds
  else [unprovedSafe]

end Diva.Report
