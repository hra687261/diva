import Diva.Parser
import Diva.Cert

/-!
# Contract files (untrusted)

`diva prove` writes a Lean file. For each top-level function `f` with a contract,
the file has:
- `f_fn`: the function, with its contract, as a `RecFun`;
- `f_body`: the proof obligation of `f` (`RecFun.BodyOk`), proved by `simp` and
  `split_omega`. If that proof fails, the user writes one by hand in the file;
- `f_correct`: `f` meets its contract (`RecFun.Meets`), from the obligations.

The parameter and the result of a function with a contract are integers. The
functions without a contract are written as values (`f_val`), because the functions
defined after them can call them.

Nothing here is trusted. Reading `f_fn` and the theorem `f_correct` in the file is
enough to know what is proved.
-/

namespace Diva.Prove

/-- `op` as a Lean operator on `Int`, or a Lean relation. -/
def binOp : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "=" | .ne => "≠" | .lt => "<" | .le => "≤" | .gt => ">" | .ge => "≥"

/-- `t` as a Lean term: an `Int`, or a `Prop` for comparisons and `&&`. -/
def term : Term → String
  | .int n => Cert.int n
  | .var x => x
  | .binop op a b => s!"({term a} {binOp op} {term b})"
  | .and a b => s!"({term a} ∧ {term b})"

/-- The terms `ts` joined by `∧`, or `True` if there are none. -/
def conj (ts : List Term) : String :=
  match ts with
  | [] => "True"
  | _ => " ∧ ".intercalate (ts.map term)

/-- The contract `sp` as a Lean term of type `FunSpec`. `x` is the name of the
    parameter. Every name of `sp` must be `x`, or the result in `ensures`. The
    argument and the result are `arg₀` and `res₀`: an OCaml name can't be one of them. -/
def funSpec (f x : String) (sp : Spec) : Except String String := do
  if sp.result == x then
    throw s!"the contract of `{f}` uses `{x}` for the parameter and for the result"
  for t in sp.requires do
    for y in t.vars do
      if y != x then throw s!"the contract of `{f}` uses `{y}` in `requires`, which isn't the parameter `{x}`"
  for t in sp.ensures do
    for y in t.vars do
      if y != x && y != sp.result then
        throw s!"the contract of `{f}` uses `{y}`, which isn't the parameter `{x}` or the result `{sp.result}`"
  return s!"\{
    pre := fun arg₀ => ∃ {x} : Int, arg₀ = .int {x} ∧ {conj sp.requires}
    post := fun arg₀ res₀ => ∃ {x} {sp.result} : Int, arg₀ = .int {x} ∧ res₀ = .int {sp.result} ∧
      {conj sp.ensures} }"

/-- What `prove` knows while it goes through the top-level items. -/
structure State where
  /-- The text of the file so far. -/
  out : Array String := #[]
  /-- The names defined so far, innermost first, with their value as a Lean term.
      `none` if the value isn't known (it isn't a function). -/
  env : List (String × Option String) := []
  /-- The Lean names of the functions with a contract so far, innermost first. -/
  fns : List String := []
  /-- The Lean defs so far (`f_fn` and `f_val`), for `simp`. -/
  defs : List String := []
  /-- The Lean names used so far for functions. -/
  used : List String := []

/-- A Lean name for the function `f` that isn't used yet: `f`, `f'`, `f''`, ... -/
partial def fresh (used : List String) (f : String) : String :=
  if used.contains f then fresh used (f ++ "'") else f

/-- The environment `env` as a Lean term, or the first name whose value isn't known. -/
def envTerm (env : List (String × Option String)) : Except String String := do
  let entries ← env.mapM fun (y, v) => match v with
    | some v => pure s!"({Cert.str y}, {v})"
    | none => throw y
  return "[" ++ ", ".intercalate entries ++ "]"

/-- The proof of `Verified .none Γ` for the functions `Γ` (their Lean names, innermost
    first), from their obligations `f_body`. -/
def verified : List String → String
  | [] => "trivial"
  | g :: Γ => s!"⟨{verified Γ}, {g}_body⟩"

/-- The Lean list of the functions `Γ` (their Lean names, innermost first). -/
def gamma (Γ : List String) : String :=
  "[" ++ ", ".intercalate (Γ.map (· ++ "_fn")) ++ "]"

/-- The proof of an obligation that `diva prove` writes: `simp` with the defs `simps`,
    then `omega`. `x` is the name of the parameter. -/
def defaultProof (x simps : String) : String :=
  s!"  intro va μ ⟨{x}, hva, hpre⟩
  subst hva
  simp [{simps}]
  all_goals split_omega"

/-- The text for the function `f` with the contract `sp`: `f_fn`, `f_body` and
    `f_correct`. `n` is its Lean name. `proofs` gives the proofs of some obligations
    (`f_body`), as tactics. The others get `defaultProof`. -/
def withContract (proofs : List (String × String)) (st : State) (n f : String)
    (s : Option String) (x : String) (body : Expr) (env : String) (sp : Spec) :
    Except String String := do
  if let some g := sp.name then
    if g != f then throw s!"the contract after `{f}` is about `{g}`"
  let several := match body with | .lam .. => true | _ => sp.params.length > 1
  if several then
    throw s!"`{f}` has a contract and several parameters: not supported yet"
  let p := sp.params.headD x
  let spec ← funSpec f p sp
  let simps := ", ".intercalate ((n ++ "_fn") :: st.defs ++
    ["wp", "BinOp.denote", "Value.isBool", "List.lookup", "callEnv", "RecFun.clos"])
  let kw := if s.isSome then "let rec" else "let"
  let proof := (proofs.lookup (n ++ "_body")).getD (defaultProof p simps)
  return s!"/-- `{kw} {f} {x} = ...`, with its contract. -/
def {n}_fn : RecFun where
  f := {match s with | some s => s!"some {Cert.str s}" | none => "none"}
  x := {Cert.str x}
  body := {Cert.expr body}
  ρ := {env}
  spec := {spec}

/-- The proof obligation of `{f}`. If the proof fails, write one by hand. -/
theorem {n}_body : {n}_fn.BodyOk .none {gamma st.fns} := by
{proof}

/-- `{f}` meets its contract: every call of `{f}` on an argument that satisfies
    `requires` gives a result that satisfies `ensures`. -/
theorem {n}_correct : {n}_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := {gamma st.fns}) ⟨{verified st.fns}, {n}_body⟩
"

/-- `prove` on one top-level item. -/
def item (proofs : List (String × String)) (st : State) : Item → Except String State
  | .expr _ => return { st with env := ("_", none) :: st.env }
  | .decl b sp => do
    let f := b.name
    -- the function: its name if it can call itself, its parameter, and its body
    let fn : Option (Option String × String × Expr) := match b with
      | .recFn f x body => some (some f, x, body)
      | .val _ (.lam x body) => some (none, x, body)
      | .val _ _ => none
    match fn, sp with
    | none, some _ => throw s!"`{f}` has a contract but isn't a function"
    | none, none => return { st with env := (f, none) :: st.env }
    | some (s, x, body), sp =>
      let n := fresh st.used f
      let st := { st with used := n :: st.used }
      match envTerm st.env, sp with
      | .error y, some _ =>
        let before := if y == "_" then "an expression `;; ...` comes before it"
          else s!"`{y}`, defined before it, isn't a function"
        throw s!"`{f}` has a contract, but {before}: not supported yet"
      | .error _, none => return { st with env := (f, none) :: st.env }
      | .ok env, some sp =>
        let text ← withContract proofs st n f s x body env sp
        return { st with out := st.out.push text, env := (f, some s!"{n}_fn.clos") :: st.env,
                         fns := n :: st.fns, defs := (n ++ "_fn") :: st.defs }
      | .ok env, none =>
        let sStr := match s with | some s => s!"some {Cert.str s}" | none => "none"
        let text := s!"/-- `{f}`, which has no contract. -/
def {n}_val : Value := .clos {sStr} {Cert.str x} {Cert.expr body} {env}
"
        return { st with out := st.out.push text, env := (f, some s!"{n}_val") :: st.env,
                         defs := (n ++ "_val") :: st.defs }

/-- The Lean file for the program whose top-level items are `items`, or why there is
    none. `proofs` gives the proofs of some obligations, as tactics. -/
def file (items : List Item) (proofs : List (String × String) := []) :
    Except String String := do
  let st ← items.foldlM (item proofs) {}
  if st.fns.isEmpty then
    throw "no function has a contract: write one in a `(*@ ... *)` comment after a function"
  return s!"import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

" ++ "\n".intercalate st.out.toList

end Diva.Prove
