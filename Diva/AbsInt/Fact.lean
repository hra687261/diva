import Diva.AbsInt.AVal
import Diva.Ast

/-!
# Facts

A fact is a formula of the contract language about one value, named `v`. For
example, `-5 <= v && v <= -4`. An LLM gives hints as facts. `ofFact` turns a fact
into an abstract value (`Flat A`), for any numeric domain `A`. So the LLM writes the
same facts whatever the domain, and whatever the type of the value.

For now the contract language only has integers, so the facts are about integers:
comparisons of `v` with an integer. A fact about another kind of value (a boolean, a
list, ...) is a new case of `ofFact`, once the contract language can write it.
-/

namespace Diva.AbsInt

open AbsDomain NumDomain

variable {A : Type} [NumDomain A]

/-- The integer that `t` is, if `t` has no names: `3`, `-5`, `2 * 4`. -/
def Term.const? : Term → Option Int
  | .int n => some n
  | .binop .add a b => return (← Term.const? a) + (← Term.const? b)
  | .binop .sub a b => return (← Term.const? a) - (← Term.const? b)
  | .binop .mul a b => return (← Term.const? a) * (← Term.const? b)
  | _ => none

/-- The integers `v` such that `v op n`, with the operations that every numeric
    domain has. For `<>`, all the integers, because the domain may not have a value
    for "all the integers but `n`". -/
def bound (op : BinOp) (n : Int) : Option A :=
  match op with
  | .le => some (assumeLe top (const n)).1
  | .lt => some (assumeLt top (const n)).1
  | .ge => some (assumeLe (const n) top).2
  | .gt => some (assumeLt (const n) top).2
  | .eq => some (const n)
  | .ne => some top
  | _ => none

/-- `n op v` is `v (flip op) n`. -/
def flip : BinOp → BinOp
  | .le => .ge
  | .lt => .gt
  | .ge => .le
  | .gt => .lt
  | op => op

/-- The values `v` such that the fact `t` holds. `t` is comparisons of `v` with an
    integer, joined by `&&`. Any other formula is an error. -/
def ofFact : Term → Except String (Flat A)
  | .and a b => return Flat.meet (← ofFact a) (← ofFact b)
  | .binop op (.var "v") b =>
    match (Term.const? b).bind (bound op) with
    | some a => .ok (Flat.ofInt a)
    | none => .error "a fact compares `v` with an integer"
  | .binop op a (.var "v") =>
    match (Term.const? a).bind (bound (flip op)) with
    | some a => .ok (Flat.ofInt a)
    | none => .error "a fact compares `v` with an integer"
  | _ => .error "a fact compares `v` with an integer, and joins the comparisons with `&&`"

end Diva.AbsInt
