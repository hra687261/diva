import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail
import Diva.Opt

/-!
# Certificates (untrusted)

A certificate is a Lean file that states, as a theorem, that a program never fails.
It contains the program and the hints of the analysis, as Lean terms. The
proof is `safe`: the kernel runs `mayFail` on the program with these hints
(`decide +kernel`), and `safe` turns its answer into the theorem.

Nothing here is trusted. If the printing were wrong, the theorem would be about
another program, or Lean would reject the proof. Reading the theorem and the program
in the file is enough to know what is proved. The kernel checks the hints again, so
the inference (`inferHints`) isn't trusted either.
-/

namespace Diva.Cert

open AbsInt

/-- `s` as a Lean string literal. -/
def str (s : String) : String := s.quote

/-- `n` as a Lean term of type `Int`, in parentheses if it is negative. -/
def int (n : Int) : String := if n < 0 then s!"({n})" else toString n

def binOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div" | .mod => ".mod"
  | .eq => ".eq" | .ne => ".ne" | .lt => ".lt" | .le => ".le" | .gt => ".gt" | .ge => ".ge"

/-- `e` as a Lean term of type `Diva.Expr`. -/
def expr : Expr → String
  | .int n => s!"(.int {int n})"
  | .bool b => s!"(.bool {b})"
  | .unit => ".unit"
  | .var x => s!"(.var {str x})"
  | .app f a => s!"(.app {expr f} {expr a})"
  | .lam x b => s!"(.lam {str x} {expr b})"
  | .letin x a b => s!"(.letin {str x} {expr a} {expr b})"
  | .letrec f x a b => s!"(.letrec {str f} {str x} {expr a} {expr b})"
  | .ite c t e => s!"(.ite {expr c} {expr t} {expr e})"
  | .binop op a b => s!"(.binop {binOp op} {expr a} {expr b})"
  | .nil => ".nil"
  | .cons a b => s!"(.cons {expr a} {expr b})"
  | .matchList s n x xs c => s!"(.matchList {expr s} {expr n} {str x} {str xs} {expr c})"
  | .assert c => s!"(.assert {expr c})"
  | .alloc site n v => s!"(.alloc {site} {expr n} {expr v})"
  | .get a i => s!"(.get {expr a} {expr i})"
  | .set a i v => s!"(.set {expr a} {expr i} {expr v})"
  | .len a => s!"(.len {expr a})"
  | .ref site v => s!"(.ref {site} {expr v})"
  | .deref r => s!"(.deref {expr r})"
  | .assign r v => s!"(.assign {expr r} {expr v})"
  | .exn t v => s!"(.exn {str t} {expr v})"
  | .raise v => s!"(.raise {expr v})"
  | .tryw a k h => s!"(.tryw {expr a} {str k} {expr h})"
  | .exnCase s t x h m => s!"(.exnCase {expr s} {str t} {str x} {expr h} {expr m})"

def bound : Bound → String
  | .negInf => ".negInf"
  | .fin n => s!"(.fin {int n})"
  | .posInf => ".posInf"

def itv : Itv → String
  | .bot => ".bot"
  | .range lo hi => s!"(.range {bound lo} {bound hi})"

/-- `a` as a Lean term of type `Flat Itv`. -/
def flat (a : Flat Itv) : String :=
  s!"\{ int := {itv a.int}, tt := {a.tt}, ff := {a.ff}, unit := {a.unit}, " ++
  s!"list := {a.list}, fn := {a.fn}, loc := {a.loc}, exn := {a.exn} }"

/-- `H` as a Lean term of type `Hints Itv`, one hint per line. -/
def hints (H : Hints Itv) : String :=
  match H with
  | [] => "[]"
  | _ => "[\n" ++ ",\n".intercalate (H.map fun (x, a) => s!"  ({str x}, {flat a})") ++ "]"

/-- The certificate of `e`, with the hints `H`: a Lean file stating that `e` never
    fails. `none` if `mayFail` says `e` may fail with `H`. -/
def certificate (H : Hints Itv) (e : Expr) : Option String :=
  if mayFail H [] e then none
  else some s!"import Diva.AbsInt.ItvDomain
import Diva.AbsInt.MayFail

/-! Certificate written by `diva cert`. The theorem `program_safe` states that the
program never fails. `mayFail`, run by the kernel with the hints, checks it. -/

/-- The program. -/
def program : Diva.Expr :=
  {expr e}

/-- The hints of the analysis. The kernel checks them again. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := {hints H}

/-- The program never fails, whatever the starting store. -/
theorem program_safe \{μ μ' : Diva.Store} \{k : Diva.Err} :
    ¬ Diva.Eval [] μ program (.err k) μ' :=
  Diva.AbsInt.safe (H := hints) (by decide +kernel)
"

/-- The certificate of the optimisation of `e`, with the hints `H`: a Lean file stating
    that `e` and its optimised version `opt H [] e` are equivalent. The kernel runs
    `opt` with `H` to check that the printed program is that version. It doesn't run
    the inference that gave `H`. -/
def optCertificate (H : Hints Itv) (e : Expr) : String :=
  s!"import Diva.AbsInt.ItvDomain
import Diva.OptSound

/-! Certificate written by `diva opt --cert`. The theorem `optimized_correct` states
that `optimized` is equivalent to `source`. -/

/-- The program. -/
def source : Diva.Expr :=
  {expr e}

/-- The hints of the analysis. `opt` uses them to choose what to rewrite. -/
def hints : Diva.AbsInt.Hints Diva.AbsInt.Itv := {hints H}

/-- The optimised program. -/
def optimized : Diva.Expr :=
  {expr (Opt.opt H ([] : AEnv Itv) e)}

/-- `opt`, run by the kernel with the hints, gives `optimized`. -/
theorem opt_source : Diva.Opt.opt hints ([] : Diva.AbsInt.AEnv Diva.AbsInt.Itv) source = optimized := by
  decide +kernel

/-- `optimized` is equivalent to `source`: if one of them gives an outcome, the other
    gives a related outcome, with related stores. Related values are equal, except
    closures, whose bodies may be optimised. -/
theorem optimized_correct : Diva.Opt.Equiv hints source optimized :=
  opt_source ▸ Diva.Opt.opt_correct hints source
"

end Diva.Cert
