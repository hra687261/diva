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

For the `i`-th top-level expression `;; e` after these functions, the file has:
- `topi_wp`: the obligation of `e`, `wp` with the postcondition `True`. Each call
  in `e` must get arguments that satisfy `requires`;
- `topi_safe`: `e` runs without error (`Holds.of_wp`).

The parameters and the result of a function with a contract are integers. A function
without a contract that a function with a contract calls gets the empty contract: no
`requires` and no `ensures`. Its proof says that it doesn't fail. The other functions
without a contract are written as values (`f_val`), because the functions defined
after them can call them.

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

/-- `i` with subscript digits: `12` gives `₁₂`. -/
def subscript (i : Nat) : String :=
  String.map (fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat)) (toString i)

/-- The names `arg₀`, `arg₁`, ... of the arguments, one for each name of `xs`.
    (We use subcrtipts because to avoid name clashes) -/
def argNames (xs : List String) : List String :=
  (List.range xs.length).map (s!"arg{subscript ·}")

/-- The contract `sp` as a Lean term of type `FunSpec`. `xs` are the names of the
    parameters in `sp`. Every name of `sp` must be one of `xs`, or the result in
    `ensures`. The arguments and the result are `arg₀`, `arg₁`, ... and `res₀`: a name
    of the program can't be one of them, because the parser doesn't accept `₀`. -/
def funSpec (f : String) (xs : List String) (sp : Spec) : Except String String := do
  if xs.eraseDups.length != xs.length then
    throw s!"the contract of `{f}` uses the same name for two parameters"
  if xs.contains sp.result then
    throw s!"the contract of `{f}` uses `{sp.result}` for a parameter and for the result"
  let params := ", ".intercalate (xs.map (s!"`{·}`"))
  for t in sp.requires do
    for y in t.vars do
      if !xs.contains y then
        throw s!"the contract of `{f}` uses `{y}` in `requires`, which isn't a parameter ({params})"
  for t in sp.ensures do
    for y in t.vars do
      if !xs.contains y && y != sp.result then
        throw s!"the contract of `{f}` uses `{y}`, which isn't a parameter ({params}) or the result `{sp.result}`"
  let args := argNames xs
  let pattern := "[" ++ ", ".intercalate args ++ "]"
  let isInt := " ∧ ".intercalate ((args.zip xs).map fun (a, x) => s!"{a} = .int {x}")
  let names := " ".intercalate xs
  return s!"\{
    pre := fun
      | {pattern} => ∃ {names} : Int, {isInt} ∧ {conj sp.requires}
      | _ => False
    post := fun
      | {pattern}, res₀ => ∃ {names} {sp.result} : Int, {isInt} ∧ res₀ = .int {sp.result} ∧
        {conj sp.ensures}
      | _, _ => False }"

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
  /-- How many top-level expressions `;; e` there were so far. -/
  exprs : Nat := 0

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
    then `omega`. `xs` are the names of the parameters in the contract. -/
def defaultProof (xs : List String) (simps : String) : String :=
  let (vs, hs) := match xs with
    | [_] => (["va"], ["hva"])
    | _ => ((argNames xs).map (·.replace "arg" "va"), (argNames xs).map (·.replace "arg" "hva"))
  s!"  intro {" ".intercalate vs} μ ⟨{", ".intercalate (xs ++ hs)}, hpre⟩
  subst {" ".intercalate hs}
  simp [{simps}]
  all_goals split_omega"

/-- The parameters of the function whose body is `body`, after its first parameter,
    and its body after them: `fun y -> fun z -> e` gives `[y, z]` and `e`. -/
def moreParams : Expr → List String × Expr
  | .lam y e => let (ys, e') := moreParams e
    (y :: ys, e')
  | e => ([], e)

/-- The text for the function `f` with the contract `sp`: `f_fn`, `f_body` and
    `f_correct`. `n` is its Lean name. `empty` says that `f` has no contract in the
    program, and `sp` is the empty contract. `inferred` says that the analysis
    inferred `sp`. `x` is its first parameter, and `body` is what
    comes after it. `proofs` gives the proofs of some obligations (`f_body`), as
    tactics. The others get `defaultProof`. -/
def withContract (proofs : List (String × String)) (st : State) (n f : String)
    (s : Option String) (x : String) (body : Expr) (env : String) (sp : Spec)
    (empty : Bool := false) (inferred : Bool := false) : Except String String := do
  if let some g := sp.name then
    if g != f then throw s!"the contract after `{f}` is about `{g}`"
  let (rest, inner) := moreParams body
  let code := x :: rest
  -- the names of the parameters in the contract: the ones of its header, if it has one
  let xs := if sp.params.isEmpty then code else sp.params
  if xs.length != code.length then
    throw s!"the contract of `{f}` has {xs.length} parameters, but `{f}` has {code.length}"
  let spec ← funSpec f xs sp
  let simps := ", ".intercalate ((n ++ "_fn") :: st.defs ++
    ["wp", "BinOp.denote", "Value.isBool", "List.lookup", "callEnv", "RecFun.clos"])
  let kw := if s.isSome then "let rec" else "let"
  let proof := (proofs.lookup (n ++ "_body")).getD (defaultProof xs simps)
  let restField := if rest.isEmpty then ""
    else s!"\n  rest := [{", ".intercalate (rest.map Cert.str)}]"
  let what :=
    if empty then s!"without a contract: it gets the empty contract. Its proof
    says that `{f}` doesn't fail on integers"
    else if inferred then "with the contract that the analysis infers (`diva hints`)"
    else "with its contract"
  return s!"/-- `{kw} {f} {" ".intercalate code} = ...`, {what}. -/
def {n}_fn : RecFun where
  name := {Cert.str f}
  f := {match s with | some s => s!"some {Cert.str s}" | none => "none"}
  x := {Cert.str x}{restField}
  body := {Cert.expr inner}
  ρ := {env}
  spec := {spec}

/-- The proof obligation of `{f}`. If the proof fails, write one by hand. -/
theorem {n}_body : {n}_fn.BodyOk .none {gamma st.fns} := by
{proof}

/-- `{f}` meets its contract: every call of `{f}` on arguments that satisfy
    `requires` gives a result that satisfies `ensures`. -/
theorem {n}_correct : {n}_fn.Meets :=
  RecFun.meets_of_verified (S := .none) (Γ := {gamma st.fns}) ⟨{verified st.fns}, {n}_body⟩
"

/-- The text for the top-level expression `e`, the `i`-th one: `topi_wp` and
    `topi_safe`. `e` runs in the environment `env`, and can call the functions with a
    contract defined so far. -/
def topExpr (st : State) (i : Nat) (e : Expr) (env : String) : String :=
  let simps := ", ".intercalate (st.defs ++
    ["wp", "BinOp.denote", "Value.isBool", "List.lookup", "callEnv", "RecFun.clos"])
  s!"/-- The obligation of the top-level expression `{ppExpr e}`. Each call in it must
    get arguments that satisfy `requires`. If the proof fails, write one by hand. -/
theorem top{i}_wp (μ : Store) :
    wp .none {gamma st.fns} {Cert.expr e} (fun _ _ => True) {env} μ := by
  simp [{simps}]
  all_goals split_omega

/-- The top-level expression `{ppExpr e}` runs without error. -/
theorem top{i}_safe (μ : Store) : Holds {Cert.expr e} (fun _ _ => True) {env} μ :=
  Holds.of_wp (S := .none) (Γ := {gamma st.fns}) {verified st.fns} (top{i}_wp μ)
"

/-- The free names of the top-level declaration `b`. In `let rec f x = e`, `f` and `x`
    are bound in `e`. -/
def declFreeNames : Binding → List String
  | .val _ e => freeNames [] e
  | .recFn f x e => freeNames [f, x] e

/-- The functions of `items` without a contract that are called by a function with a
    contract, or by a function of this list. -/
def calledWithoutContract (items : List Item) : List String :=
  let decls := items.filterMap fun | .decl b sp => some (b, sp.isSome) | .expr _ => none
  -- `called`: the functions found so far. Each step adds the ones that they call.
  let step (called : List String) : List String :=
    called ++ (decls.flatMap fun (b, has) =>
      if has || called.contains b.name then
        (declFreeNames b).filter fun y =>
          !called.contains y && decls.any fun (c, hasC) => c.name == y && !hasC
      else []).eraseDups
  (decls.foldl (fun called _ => step called) []).eraseDups

/-- `prove` on one top-level item. `called` are the functions without a contract that
    a function with a contract calls. `file` computes them with `calledWithoutContract`.
    Each one gets the empty contract: integer parameters and result, with no
    `requires` and no `ensures`. Its proof says that it doesn't fail. `inferred` are
    the functions whose contract the analysis inferred (`SpecOfHints`). -/
def item (proofs : List (String × String)) (called inferred : List String) (st : State) :
    Item → Except String State
  | .expr e =>
    let i := st.exprs + 1
    let st' := { st with env := ("_", none) :: st.env, exprs := i }
    -- an expression before the functions with a contract, or after a name that isn't
    -- a function, gets no obligation
    match st.fns, envTerm st.env with
    | _ :: _, .ok env => return { st' with out := st'.out.push (topExpr st i e env) }
    | _, _ => return st'
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
        let text ← withContract proofs st n f s x body env sp (inferred := inferred.contains f)
        return { st with out := st.out.push text, env := (f, some s!"{n}_fn.clos") :: st.env,
                         fns := n :: st.fns, defs := (n ++ "_fn") :: st.defs }
      | .ok env, none =>
        if called.contains f then
          let text ← withContract proofs st n f s x body env {} (empty := true)
          return { st with out := st.out.push text, env := (f, some s!"{n}_fn.clos") :: st.env,
                           fns := n :: st.fns, defs := (n ++ "_fn") :: st.defs }
        let sStr := match s with | some s => s!"(some {Cert.str s})" | none => "none"
        let text := s!"/-- `{f}`, which has no contract. -/
def {n}_val : Value := .clos {sStr} {Cert.str x} {Cert.expr body} {env}
"
        return { st with out := st.out.push text, env := (f, some s!"{n}_val") :: st.env,
                         defs := (n ++ "_val") :: st.defs }

/-- The Lean file for the program whose top-level items are `items`, or why there is
    none. `proofs` gives the proofs of some obligations, as tactics. `inferred` are the
    functions whose contract the analysis inferred. -/
def file (items : List Item) (proofs : List (String × String) := [])
    (inferred : List String := []) : Except String String := do
  let st ← items.foldlM (item proofs (calledWithoutContract items) inferred) {}
  if st.fns.isEmpty then
    throw "no function has a contract: write one in a `(*@ ... *)` comment after a function"
  return s!"import Diva.Wp

/-! Written by `diva prove`. For each function `f` with a contract, `f_fn` is the
function, and the theorem `f_correct` states that `f` meets its contract. `f_body` is
the proof obligation of `f`. If its proof fails, write one by hand. -/

open Diva

" ++ "\n".intercalate st.out.toList

end Diva.Prove
