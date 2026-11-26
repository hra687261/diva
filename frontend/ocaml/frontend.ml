(* The OCaml frontend of DIVA (untrusted).

   [ocaml-frontend FILE.ml] parses and type-checks FILE.ml with the OCaml compiler's own
   libraries ([compiler-libs]), translates it to DIVA's core language, and prints the
   result as S-expressions, in the format of [Diva/Sexp.lean]. A construct that it
   doesn't translate stops it, with its position and exit code 1. An OCaml error (a
   syntax or type error) is printed as the compiler prints it, with exit code 2.

   The translation keeps the constructs of DIVA's own syntax, desugared as DIVA's
   parser does ([Diva/Parser.lean]): [a && b] is [if a then b else false], [for] is a
   recursive function, ... So on a program in DIVA's syntax, [diva ocaml print] and
   [diva print] give almost the same program.

   Build: frontend/ocaml/build.sh *)

open Typedtree

(* A construct that the translation doesn't support, with its position. *)
exception Unsupported of Location.t * string

let unsupported loc fmt =
  Format.kasprintf (fun s -> raise (Unsupported (loc, s))) fmt

(**** DIVA's core language ****)

(* [expr] is [Expr] in [Diva/Ast.lean], with the part of the file that each expression
   comes from. [to_sexp] prints it in the format of [Diva/Sexp.lean]: it is the only
   place with the names of that format. *)

type op = Add | Sub | Mul | Div | Mod | Eq | Ne | Lt | Le | Gt | Ge

type expr = { loc : Location.t; desc : desc }

and desc =
  | Int of int64
  | Bool of bool
  | Unit
  | Nil
  | Var of string
  | App of expr * expr
  | Lam of string * expr
  | Letin of string * expr * expr
  | Letrec of string * string * expr * expr  (** [let rec f x = b in e] *)
  | Ite of expr * expr * expr
  | Binop of op * expr * expr
  | Cons of expr * expr
  | MatchList of expr * expr * string * string * expr
      (** [match s with [] -> n | x :: xs -> c] *)
  | Assert of expr
  | Alloc of expr * expr  (** [Array.make n v] *)
  | Get of expr * expr
  | Set of expr * expr * expr
  | Len of expr
  | Ref of expr
  | Deref of expr
  | Assign of expr * expr
  | Ctor of string * expr  (** the constructor [C] applied to [v] *)
  | Raise of expr
  | Try of expr * string * expr  (** [try a with k -> h] *)
  | CtorCase of expr * string * string * expr * expr
      (** [match s with C x -> h | _ -> m] *)
  | Overflow of int * expr
      (** [e], an integer of [bits] bits: DIVA checks that its value fits, if it
          may not ([Overflow.wrap]) *)

(* A top-level item, with the text of its contract, if it has one. *)
type item =
  | Let_item of string * expr * string option
  | Letrec_item of string * string * expr * string option
  | Expr_item of expr

let op_name = function
  | Add -> "add"
  | Sub -> "sub"
  | Mul -> "mul"
  | Div -> "div"
  | Mod -> "mod"
  | Eq -> "eq"
  | Ne -> "ne"
  | Lt -> "lt"
  | Le -> "le"
  | Gt -> "gt"
  | Ge -> "ge"

(**** S-expressions ****)

type sexp = Atom of string | Str of string | List of sexp list

let rec print buf = function
  | Atom a -> Buffer.add_string buf a
  | Str s ->
      Buffer.add_char buf '"';
      String.iter
        (fun c ->
          if c = '"' || c = '\\' then Buffer.add_char buf '\\';
          Buffer.add_char buf c)
        s;
      Buffer.add_char buf '"'
  | List xs ->
      Buffer.add_char buf '(';
      List.iteri
        (fun i x ->
          if i > 0 then Buffer.add_char buf ' ';
          print buf x)
        xs;
      Buffer.add_char buf ')'

(* [e] as [(KIND START STOP args...)], for its part of the file. *)
let rec to_sexp (e : expr) =
  let node kind args =
    List
      (Atom kind
      :: Atom (string_of_int e.loc.loc_start.pos_cnum)
      :: Atom (string_of_int e.loc.loc_end.pos_cnum)
      :: args)
  in
  let s = to_sexp in
  match e.desc with
  | Int n -> node "int" [ Atom (Int64.to_string n) ]
  | Bool b -> node "bool" [ Atom (string_of_bool b) ]
  | Unit -> node "unit" []
  | Nil -> node "nil" []
  | Var x -> node "var" [ Str x ]
  | App (f, a) -> node "app" [ s f; s a ]
  | Lam (x, b) -> node "lam" [ Str x; s b ]
  | Letin (x, a, b) -> node "letin" [ Str x; s a; s b ]
  | Letrec (f, x, b, e) -> node "letrec" [ Str f; Str x; s b; s e ]
  | Ite (c, t, f) -> node "ite" [ s c; s t; s f ]
  | Binop (op, a, b) -> node "binop" [ Atom (op_name op); s a; s b ]
  | Cons (a, b) -> node "cons" [ s a; s b ]
  | MatchList (l, n, x, xs, c) ->
      node "matchList" [ s l; s n; Str x; Str xs; s c ]
  | Assert c -> node "assert" [ s c ]
  | Alloc (n, v) -> node "alloc" [ s n; s v ]
  | Get (a, i) -> node "get" [ s a; s i ]
  | Set (a, i, v) -> node "set" [ s a; s i; s v ]
  | Len a -> node "len" [ s a ]
  | Ref v -> node "ref" [ s v ]
  | Deref r -> node "deref" [ s r ]
  | Assign (r, v) -> node "assign" [ s r; s v ]
  | Ctor (c, v) -> node "ctor" [ Str c; s v ]
  | Raise v -> node "raise" [ s v ]
  | Try (a, k, h) -> node "tryw" [ s a; Str k; s h ]
  | CtorCase (v, c, x, h, m) -> node "ctorCase" [ s v; Str c; Str x; s h; s m ]
  | Overflow (bits, e) -> node "overflow" [ Atom (string_of_int bits); s e ]

let spec_sexp = function Some s -> [ Str s ] | None -> []

let item_to_sexp = function
  | Let_item (f, e, spec) ->
      List ([ Atom "let"; Str f; to_sexp e ] @ spec_sexp spec)
  | Letrec_item (f, x, b, spec) ->
      List ([ Atom "letrec"; Str f; Str x; to_sexp b ] @ spec_sexp spec)
  | Expr_item e -> List [ Atom "expr"; to_sexp e ]

(**** Building expressions ****)

let mk loc desc = { loc; desc }
let var loc x = mk loc (Var x)
let int loc n = mk loc (Int (Int64.of_int n))
let bool loc b = mk loc (Bool b)
let unit loc = mk loc Unit
let letin loc x a b = mk loc (Letin (x, a, b))
let seq loc a b = letin loc "_" a b
let ite loc c t e = mk loc (Ite (c, t, e))
let binop loc op a b = mk loc (Binop (op, a, b))
let app loc f a = mk loc (App (f, a))
let overflow loc bits e = mk loc (Overflow (bits, e))

(* [a op b] on integers of [bits] bits. *)
let arith loc bits op a b = overflow loc bits (binop loc op a b)

(* A new name. Names that start with [%] can't be written in OCaml, so they hide no
   name of the program. *)
let fresh =
  let n = ref 0 in
  fun () ->
    incr n;
    Printf.sprintf "%%t%d" !n

(**** Types ****)

(* The type [ty] is [int], [char], [Int32.t] or [Int64.t] ([`Int]), [bool], [unit], a
   type variable such as ['a], or another one. *)
let kind env ty =
  match Types.get_desc (Ctype.expand_head env ty) with
  | Tconstr (p, [], _)
    when List.exists (Path.same p)
           [
             Predef.path_int;
             Predef.path_char;
             Predef.path_int32;
             Predef.path_int64;
           ] ->
      `Int
  | Tconstr (p, [], _) when Path.same p Predef.path_bool -> `Bool
  | Tconstr (p, [], _) when Path.same p Predef.path_unit -> `Unit
  | Tvar _ -> `Var
  | _ -> `Other

(**** Expressions ****)

(* The operators of DIVA. DIVA's [=] and [<>] work on integers, booleans and [()], and
   its other comparisons only on integers. On other values, they stop the program with a
   type error. So a comparison on another type is rejected: it would always fail. On a
   type variable ['a], it is accepted: DIVA's result is OCaml's, or a failure that DIVA
   reports. *)
let binops =
  [
    ("Stdlib.+", Add);
    ("Stdlib.-", Sub);
    ("Stdlib.*", Mul);
    ("Stdlib./", Div);
    ("Stdlib.mod", Mod);
    ("Stdlib.=", Eq);
    ("Stdlib.<>", Ne);
    ("Stdlib.<", Lt);
    ("Stdlib.<=", Le);
    ("Stdlib.>", Gt);
    ("Stdlib.>=", Ge);
  ]

(* The integer constants of the library. *)
let constants =
  [
    ("Stdlib.max_int", Int64.of_int max_int);
    ("Stdlib.min_int", Int64.of_int min_int);
    ("Stdlib.Int32.zero", 0L);
    ("Stdlib.Int32.one", 1L);
    ("Stdlib.Int32.minus_one", -1L);
    ("Stdlib.Int32.max_int", Int64.of_int32 Int32.max_int);
    ("Stdlib.Int32.min_int", Int64.of_int32 Int32.min_int);
    ("Stdlib.Int64.zero", 0L);
    ("Stdlib.Int64.one", 1L);
    ("Stdlib.Int64.minus_one", -1L);
    ("Stdlib.Int64.max_int", Int64.max_int);
    ("Stdlib.Int64.min_int", Int64.min_int);
  ]

(* The modules of integers with a fixed number of bits other than [int]'s 63, and
   their functions: [Int32.add], ... *)
let int_modules = [ ("Stdlib.Int32.", 32); ("Stdlib.Int64.", 64) ]

let int_functions =
  [ ("add", Add); ("sub", Sub); ("mul", Mul); ("div", Div); ("rem", Mod) ]

(* The module of [p] in [int_modules], with its number of bits, and the name of [p] in
   it: [Stdlib.Int32.add] gives [32] and [add]. *)
let int_module p =
  List.find_map
    (fun (m, bits) ->
      if String.starts_with ~prefix:m p then
        Some
          ( bits,
            String.sub p (String.length m) (String.length p - String.length m)
          )
      else None)
    int_modules

let output_functions =
  [
    "Stdlib.print_int";
    "Stdlib.print_string";
    "Stdlib.print_endline";
    "Stdlib.print_newline";
    "Stdlib.print_char";
  ]

(* The name of [p], such as [Stdlib.mod], from its parts. [Path.name] writes a keyword
   used as a name after [\#]: [Stdlib.\#mod]. *)
let path_name p =
  match Path.flatten p with
  | `Ok (id, parts) -> String.concat "." (Ident.name id :: parts)
  | `Contains_apply -> Path.name p

(* The name of the library function [f], if [f] is one, such as [Stdlib.+]. *)
let library f =
  match f.exp_desc with
  | Texp_ident ((Path.Pdot _ as p), _, _) -> Some (path_name p)
  | _ -> None

(* The library functions that can fail on integers only by overflow: [/] and [mod]
   also fail on [0]. An overflow is a failed check, a fatal error. *)
let total = [ "Stdlib.+"; "Stdlib.-"; "Stdlib.*"; "Stdlib.~-" ]

(* [e] is computed without any effect: no error but an overflow, no read or change of
   the store, and it finishes. So it can be computed earlier or later: if two parts
   overflow, both orders give the same error. In a program that DIVA proves never
   fails, nothing overflows. *)
let rec trivial e =
  match e.exp_desc with
  | Texp_ident (Path.Pident _, _, _) | Texp_constant _ | Texp_function _ -> true
  | Texp_construct (_, _, args) -> List.for_all trivial args
  | Texp_tuple es -> List.for_all (fun (_, e) -> trivial e) es
  | Texp_apply (f, args) -> (
      match library f with
      | Some p when List.mem p total ->
          List.for_all
            (function Asttypes.Nolabel, Arg a -> trivial a | _ -> false)
            args
      | _ -> false)
  | _ -> false

(* The name bound by the pattern [p], if [p] is a name, [_] or [()]. *)
let simple_name (p : pattern) =
  match p.pat_desc with
  | Tpat_var (id, _, _) -> Some (Ident.name id)
  (* [(x : t)] is [(_ : t) as x] *)
  | Tpat_alias ({ pat_desc = Tpat_any; _ }, id, _, _, _) -> Some (Ident.name id)
  | Tpat_any -> Some "_"
  | Tpat_construct (_, cd, [], _) when cd.cstr_name = "()" -> Some "_"
  | _ -> None

let pat_name (p : pattern) =
  match simple_name p with
  | Some x -> x
  | None -> unsupported p.pat_loc "this pattern here (only a name, `_` or `()`)"

(**** Constructors and tuples ****)

(* A value of a variant type, such as [option], and an exception are constructors applied
   to an argument: [C] is [Ctor ("C", unit)], [C a] is [Ctor ("C", a)], and [C (a, b)] is
   [Ctor ("C", (a, b))]. A tuple [(a, b)] is [Ctor ("%2", [a; b])]. *)

(* The constructors seen so far, by name: an exception or the type of the variant. *)
let ctors : (string, string) Hashtbl.t = Hashtbl.create 16

(* The name of the constructor [cd]. DIVA tells constructors apart by their name
   only, so two constructors with the same name are rejected. *)
let ctor_name loc (cd : Data_types.constructor_description) =
  if cd.cstr_generalized || cd.cstr_existentials <> [] then
    unsupported loc "GADTs";
  if cd.cstr_inlined <> None then unsupported loc "records (for now)";
  let unique = function
    | Path.Pident id -> Ident.unique_name id
    | p -> Path.name p
  in
  let owner =
    match cd.cstr_tag with
    | Cstr_extension (p, _) -> "the exception " ^ unique p
    | _ -> "the type " ^ unique (Data_types.cstr_res_type_path cd)
  in
  (match Hashtbl.find_opt ctors cd.cstr_name with
  | Some o when o <> owner ->
      unsupported loc
        "two constructors named `%s`: it tells constructors apart by their \
         names only"
        cd.cstr_name
  | _ -> Hashtbl.replace ctors cd.cstr_name owner);
  cd.cstr_name

(* The constructor of the tuples of [n] components. *)
let tuple_ctor n = Printf.sprintf "%%%d" n

(* The list [[a1; ...; an]]. *)
let list loc es =
  List.fold_right (fun e l -> mk loc (Cons (e, l))) es (mk loc Nil)

(* The tuple [(a1, ..., an)]. *)
let tuple loc es = mk loc (Ctor (tuple_ctor (List.length es), list loc es))

(* What happens when no case of a [match] matches: OCaml raises [Match_failure]. *)
let match_failure loc =
  mk loc (Raise (mk loc (Ctor ("Match_failure", unit loc))))

(* The translation of [e]. The sub-expressions are translated from the first to the
   last, with [let]: OCaml computes the arguments of a function from the last to the
   first. So the first construct that isn't supported is the one reported. *)
let rec expr (e : expression) : expr =
  let loc = e.exp_loc in
  match e.exp_desc with
  | Texp_ident (Path.Pident id, _, _) -> var loc (Ident.name id)
  | Texp_ident (p, _, _) when List.mem_assoc (path_name p) constants ->
      mk loc (Int (List.assoc (path_name p) constants))
  | Texp_ident (p, _, _) ->
      unsupported loc "the library function `%s`, except when it is called"
        (path_name p)
  | Texp_constant (Const_int n) -> int loc n
  | Texp_constant (Const_int32 n) -> mk loc (Int (Int64.of_int32 n))
  | Texp_constant (Const_int64 n) -> mk loc (Int n)
  | Texp_constant (Const_char c) -> int loc (Char.code c)
  | Texp_constant _ ->
      unsupported loc "this constant (only integers and characters)"
  | Texp_construct (_, cd, args) -> construct loc cd args
  | Texp_let (Nonrecursive, [ vb ], body) -> (
      let a = expr vb.vb_expr in
      match simple_name vb.vb_pat with
      | Some x -> letin loc x a (expr body)
      | None ->
          let v = fresh () in
          letin loc v a (pattern vb.vb_pat v (expr body) (match_failure loc)))
  | Texp_let (Recursive, [ vb ], body) ->
      let f, x, b = rec_fun vb in
      mk loc (Letrec (f, x, b, expr body))
  | Texp_let _ -> unsupported loc "`let ... and ...`"
  | Texp_function (params, body) -> lams loc params body
  | Texp_apply (f, args) ->
      let arg = function
        | Asttypes.Nolabel, Arg a -> a
        | _ -> unsupported loc "labelled and optional arguments"
      in
      apply loc f (List.map arg args)
  | Texp_ifthenelse (c, t, f) ->
      let c = expr c in
      let t = expr t in
      ite loc c t (match f with Some f -> expr f | None -> unit loc)
  | Texp_sequence (a, b) ->
      let a = expr a in
      seq loc a (expr b)
  | Texp_assert (c, _) -> mk loc (Assert (expr c))
  | Texp_match (s, cases, [], _) ->
      let value (c : computation case) =
        match split_pattern c.c_lhs with
        | Some p, None -> { c with c_lhs = p }
        | _ -> unsupported c.c_lhs.pat_loc "`exception` patterns"
      in
      match_ loc s (List.map value cases)
  | Texp_try (a, cases, []) ->
      let k = "%exn" in
      let a = expr a in
      mk loc (Try (a, k, match_cases loc k cases (mk loc (Raise (var loc k)))))
  | Texp_while (c, b) ->
      (* as DIVA's parser: [let rec %while _ = if c then (b; %while ()) else () in
       %while ()] *)
      let c = expr c in
      let next = app loc (var loc "%while") (unit loc) in
      mk loc
        (Letrec
           ("%while", "_", ite loc c (seq loc (expr b) next) (unit loc), next))
  | Texp_for (id, _, lo, hi, dir, b) ->
      (* as DIVA's parser: [let %lo = lo in let %hi = hi in
       let rec %for i = if i <= %hi then (b; %for (i + 1)) else () in %for %lo] *)
      let i = Ident.name id in
      let lo = expr lo in
      let hi = expr hi in
      let cmp, step =
        match dir with Upto -> (Le, Add) | Downto -> (Ge, Sub)
      in
      let next =
        app loc (var loc "%for") (binop loc step (var loc i) (int loc 1))
      in
      let loop =
        mk loc
          (Letrec
             ( "%for",
               i,
               ite loc
                 (binop loc cmp (var loc i) (var loc "%hi"))
                 (seq loc (expr b) next)
                 (unit loc),
               app loc (var loc "%for") (var loc "%lo") ))
      in
      letin loc "%lo" lo (letin loc "%hi" hi loop)
  | Texp_tuple es ->
      let es =
        List.map
          (function
            | None, e -> e | Some _, _ -> unsupported loc "labelled tuples")
          es
      in
      ordered loc es (tuple loc)
  | Texp_record _ | Texp_field _ | Texp_setfield _ ->
      unsupported loc "records (for now)"
  | Texp_array _ -> unsupported loc "array literals (for now)"
  | _ -> unsupported loc "this expression"

(* [C args], for the constructor [cd]. *)
and construct loc cd args =
  match (cd.cstr_name, args) with
  | "true", [] -> bool loc true
  | "false", [] -> bool loc false
  | "()", [] -> unit loc
  | "[]", [] -> mk loc Nil
  | "::", [ a; b ] ->
      ordered loc [ a; b ] (function
        | [ a; b ] -> mk loc (Cons (a, b))
        | _ -> assert false)
  | _, [] -> mk loc (Ctor (ctor_name loc cd, unit loc))
  | _, [ a ] ->
      let c = ctor_name loc cd in
      mk loc (Ctor (c, arg a))
  | _, args ->
      let c = ctor_name loc cd in
      ordered loc args (fun l -> mk loc (Ctor (c, tuple loc l)))

(* An argument of an exception or of an output function. A string is [()]: DIVA has
   no strings. *)
and arg a =
  match a.exp_desc with
  | Texp_constant (Const_string _) -> unit a.exp_loc
  | _ -> expr a

(* [fun x1 -> ... -> body]. [function cases] adds a parameter, matched by the cases. *)
and lams loc params body =
  match params with
  | p :: ps -> (
      match (p.fp_arg_label, p.fp_kind) with
      | Nolabel, Tparam_pat pat -> (
          match simple_name pat with
          | Some x -> mk loc (Lam (x, lams loc ps body))
          | None ->
              let v = fresh () in
              mk loc
                (Lam
                   ( v,
                     pattern pat v (lams loc ps body)
                       (match_failure pat.pat_loc) )))
      | _ -> unsupported p.fp_loc "labelled and optional parameters")
  | [] -> (
      match body with
      | Tfunction_body b -> expr b
      | Tfunction_cases { cases; loc = cloc; _ } ->
          let x = fresh () in
          mk loc (Lam (x, match_cases cloc x cases (match_failure cloc))))

(* [let rec f x = b]: the name of the function, its first parameter, and the rest. *)
and rec_fun vb =
  let f = pat_name vb.vb_pat in
  match vb.vb_expr.exp_desc with
  | Texp_function _ -> (
      match expr vb.vb_expr with
      | { desc = Lam (x, b); _ } -> (f, x, b)
      | _ -> assert false)
  | _ -> unsupported vb.vb_loc "`let rec` of a value that isn't a function"

(* The parts [es] of an expression, given to [k]. OCaml computes them from the last to
   the first, and DIVA from the first to the last. The order matters only when two of
   them aren't trivial. Then each one that isn't is first bound by [let], from the
   last to the first. *)
and ordered loc es k =
  if List.length (List.filter (fun e -> not (trivial e)) es) <= 1 then
    k (List.map expr es)
  else
    let parts =
      List.map
        (fun e ->
          if trivial e then (None, expr e) else (Some (fresh ()), expr e))
        es
    in
    let args =
      List.map
        (fun (x, s) -> match x with Some x -> var loc x | None -> s)
        parts
    in
    (* the last part is computed first, so its [let] is the outermost one *)
    List.fold_left
      (fun body (x, s) ->
        match x with Some x -> letin loc x s body | None -> body)
      (k args) parts

(* [k r], where [r] is the reference [e], used twice. *)
and with_name loc e k =
  if trivial e then k (expr e)
  else
    let x = fresh () in
    letin loc x (expr e) (k (var loc x))

(* The call [f args]. *)
and apply loc f args =
  let two a b k =
    ordered loc [ a; b ] (function [ a; b ] -> k a b | _ -> assert false)
  in
  match (library f, args) with
  | Some p, [ a; b ] when List.mem_assoc p binops ->
      let op = List.assoc p binops in
      (match (op, kind a.exp_env a.exp_type) with
      | _, (`Int | `Var) | (Eq | Ne), (`Bool | `Unit) -> ()
      | _ -> unsupported loc "`%s` on this type" p);
      two a b (fun a b -> arith loc 63 op a b)
  | Some "Stdlib.&&", [ a; b ] ->
      let a = expr a in
      ite loc a (expr b) (bool loc false)
  | Some "Stdlib.||", [ a; b ] ->
      let a = expr a in
      ite loc a (bool loc true) (expr b)
  | Some "Stdlib.not", [ a ] ->
      ite loc (expr a) (bool loc false) (bool loc true)
  | Some "Stdlib.~-", [ a ] ->
      overflow loc 63 (binop loc Sub (int loc 0) (expr a))
  | Some "Stdlib.ref", [ v ] -> mk loc (Ref (expr v))
  | Some "Stdlib.!", [ r ] -> mk loc (Deref (expr r))
  | Some "Stdlib.:=", [ r; v ] -> two r v (fun r v -> mk loc (Assign (r, v)))
  | Some (("Stdlib.incr" | "Stdlib.decr") as p), [ r ] ->
      let op = if p = "Stdlib.incr" then Add else Sub in
      with_name loc r (fun r ->
          mk loc (Assign (r, arith loc 63 op (mk loc (Deref r)) (int loc 1))))
  | Some "Stdlib.raise", [ v ] -> mk loc (Raise (expr v))
  | Some "Stdlib.failwith", [ s ] ->
      mk loc (Raise (mk loc (Ctor ("Failure", arg s))))
  | Some "Stdlib.invalid_arg", [ s ] ->
      mk loc (Raise (mk loc (Ctor ("Invalid_argument", arg s))))
  | Some "Stdlib.ignore", [ a ] -> seq loc (expr a) (unit loc)
  | Some p, [ a ] when List.mem p output_functions -> seq loc (arg a) (unit loc)
  | Some "Stdlib.Char.code", [ a ] -> expr a
  | Some p, _ when Option.is_some (int_module p) -> (
      let bits, name = Option.get (int_module p) in
      match (name, args) with
      | n, [ a; b ] when List.mem_assoc n int_functions ->
          two a b (fun a b -> arith loc bits (List.assoc n int_functions) a b)
      | "neg", [ a ] -> overflow loc bits (binop loc Sub (int loc 0) (expr a))
      (* [Int32.of_int] wraps an [int] that doesn't fit in 32 bits *)
      | "of_int", [ a ] ->
          if bits < 63 then overflow loc bits (expr a) else expr a
      (* [Int64.to_int] wraps an [Int64.t] that doesn't fit in 63 bits *)
      | "to_int", [ a ] ->
          if bits > 63 then overflow loc 63 (expr a) else expr a
      | _ -> unsupported loc "the library function `%s`" p)
  | Some "Stdlib.Array.make", [ n; v ] ->
      two n v (fun n v -> mk loc (Alloc (n, v)))
  | Some "Stdlib.Array.length", [ a ] -> mk loc (Len (expr a))
  | Some "Stdlib.Array.get", [ a; i ] ->
      two a i (fun a i -> mk loc (Get (a, i)))
  | Some "Stdlib.Array.set", [ a; i; v ] ->
      ordered loc [ a; i; v ] (function
        | [ a; i; v ] -> mk loc (Set (a, i, v))
        | _ -> assert false)
  | Some p, _ -> unsupported loc "the library function `%s`" p
  | None, _ ->
      ordered loc (f :: args) (function
        | f :: args -> List.fold_left (app loc) f args
        | [] -> assert false)

(* [match s with cases]. *)
and match_ loc s cases =
  (* the name of [s] in the tests: [s] itself if it is a name that no case hides *)
  let bound =
    List.concat_map
      (fun c -> List.map Ident.name (pat_bound_idents c.c_lhs))
      cases
  in
  match s.exp_desc with
  | Texp_ident (Path.Pident id, _, _) when not (List.mem (Ident.name id) bound)
    ->
      match_cases loc (Ident.name id) cases (match_failure loc)
  | _ ->
      let v = fresh () in
      let s = expr s in
      letin loc v s (match_cases loc v cases (match_failure loc))

(* The cases of a [match] on the name [v]. [final] is what happens if no case matches:
   it is copied, so it must be small. [[] -> n | x :: xs -> c] (in any order) is DIVA's
   [match] on lists. *)
and match_cases loc v cases final =
  let ctor (c : value case) =
    match (c.c_lhs.pat_desc, c.c_guard) with
    | Tpat_construct (_, cd, ps, _), None -> Some (cd.cstr_name, ps)
    | _ -> None
  in
  let simple ps = List.for_all (fun p -> simple_name p <> None) ps in
  match cases with
  | [ c1; c2 ]
    when match (ctor c1, ctor c2) with
         | Some ("[]", _), Some ("::", ps) | Some ("::", ps), Some ("[]", _) ->
             simple ps
         | _ -> false -> (
      let nil, cons =
        match ctor c1 with Some ("[]", _) -> (c1, c2) | _ -> (c2, c1)
      in
      match ctor cons with
      | Some (_, [ x; xs ]) ->
          let n = expr nil.c_rhs in
          mk loc
            (MatchList (var loc v, n, pat_name x, pat_name xs, expr cons.c_rhs))
      | _ -> assert false)
  | _ -> case_list loc v cases final

(* The cases, tried one after the other. When a case doesn't match, the next ones are
   tried: they are the code [next], or, if [next] would be copied, a function [%tN] that
   the case calls. *)
and case_list loc v cases final =
  match cases with
  | [] -> final
  | c :: rest ->
      let next, define =
        if rest = [] then (final, fun e -> e)
        else if uses c <= 1 then (case_list loc v rest final, fun e -> e)
        else
          let k = fresh () in
          let f = mk loc (Lam ("_", case_list loc v rest final)) in
          (app loc (var loc k) (unit loc), fun e -> letin loc k f e)
      in
      let ok =
        match c.c_guard with
        | None -> expr c.c_rhs
        | Some g ->
            let g = expr g in
            ite loc g (expr c.c_rhs) next
      in
      define (pattern c.c_lhs v ok next)

(* The number of times the test of the case [c] uses the code for "doesn't match". *)
and uses (c : value case) = pat_uses c.c_lhs + if c.c_guard = None then 0 else 1

and pat_uses (p : pattern) =
  let sum ps = List.fold_left (fun n p -> n + pat_uses p) 0 ps in
  match p.pat_desc with
  | Tpat_any | Tpat_var _ -> 0
  | Tpat_alias (q, _, _, _, _) -> pat_uses q
  | Tpat_constant _ -> 1
  | Tpat_tuple ps -> tuple_uses (List.map snd ps)
  | Tpat_construct (_, cd, ps, _) -> (
      match (cd.cstr_name, ps) with
      | "()", _ -> 0
      | ("true" | "false" | "[]"), _ -> 1
      | "::", _ -> 1 + sum ps
      | _, ([] | [ _ ]) -> 1 + sum ps
      | _, _ -> 1 + tuple_uses ps)
  | Tpat_or (_, q, _) -> pat_uses q
  | _ -> 0

(* a tuple: its constructor, then a [match] on each component *)
and tuple_uses ps =
  1 + List.length ps + List.fold_left (fun n p -> n + pat_uses p) 0 ps

(* The test of the pattern [p] on the value of the name [v]: [ok] if it matches, with the
   names of [p] bound, else [ko]. [ko] is copied: it must be small. Its names are names
   that start with [%]: [p] doesn't hide them. *)
and pattern (p : pattern) v ok ko =
  let loc = p.pat_loc in
  match p.pat_desc with
  | Tpat_any -> ok
  | Tpat_var (id, _, _) when Ident.name id = v -> ok
  | Tpat_var (id, _, _) -> letin loc (Ident.name id) (var loc v) ok
  | Tpat_alias (q, id, _, _, _) ->
      letin loc (Ident.name id) (var loc v) (pattern q v ok ko)
  | Tpat_constant c ->
      let n =
        match c with
        | Const_int n -> Int64.of_int n
        | Const_char c -> Int64.of_int (Char.code c)
        | Const_int32 n -> Int64.of_int32 n
        | Const_int64 n -> n
        | _ -> unsupported loc "this constant (only integers and characters)"
      in
      ite loc (binop loc Eq (var loc v) (mk loc (Int n))) ok ko
  | Tpat_tuple ps ->
      let ps =
        List.map
          (function
            | None, p -> p | Some _, _ -> unsupported loc "labelled tuples")
          ps
      in
      tuple_pattern loc ps v ok ko
  | Tpat_construct (_, cd, ps, _) -> (
      match (cd.cstr_name, ps) with
      | "true", [] -> ite loc (var loc v) ok ko
      | "false", [] -> ite loc (var loc v) ko ok
      | "()", [] -> ok
      | "[]", [] -> mk loc (MatchList (var loc v, ok, "_", "_", ko))
      | "::", [ ph; pt ] ->
          let h = name_for ph and t = name_for pt in
          mk loc
            (MatchList
               (var loc v, ko, h, t, pattern ph h (pattern pt t ok ko) ko))
      | _ ->
          let c = ctor_name loc cd in
          let x, inner =
            match ps with
            | [] -> ("_", ok)
            | [ q ] ->
                let x = name_for q in
                (x, pattern q x ok ko)
            | ps ->
                let x = fresh () in
                (x, tuple_pattern loc ps x ok ko)
          in
          mk loc (CtorCase (var loc v, c, x, inner, ko)))
  | Tpat_or (p1, p2, _) -> pattern p1 v ok (pattern p2 v ok ko)
  | Tpat_record _ -> unsupported loc "records (for now)"
  | Tpat_array _ -> unsupported loc "array patterns"
  | _ -> unsupported loc "this pattern"

(* The test of the tuple pattern [(p1, ..., pn)] on [v]. *)
and tuple_pattern loc ps v ok ko =
  let l = fresh () in
  let rec components l = function
    | [] -> ok
    | p :: ps ->
        let h = name_for p in
        let t = if ps = [] then "_" else fresh () in
        mk loc
          (MatchList (var loc l, ko, h, t, pattern p h (components t ps) ko))
  in
  mk loc
    (CtorCase (var loc v, tuple_ctor (List.length ps), l, components l ps, ko))

(* The name for the value that the pattern [p] tests: the name of [p] if it is a name,
   else a new name. *)
and name_for (p : pattern) =
  match p.pat_desc with
  | Tpat_var (id, _, _) -> Ident.name id
  | Tpat_any -> "_"
  | _ -> fresh ()

(**** Top-level items ****)

(* The text of the comment at [loc], after spaces and newlines that replace the text
   of the file before it. So a parse error in the contract has its position in the
   file. A UTF-8 character before the comment is one space. *)
let comment_text src (loc : Location.t) =
  let start = loc.loc_start.pos_cnum and stop = loc.loc_end.pos_cnum in
  let pad = Buffer.create start in
  String.iteri
    (fun i c ->
      if i < start then
        if c = '\n' then Buffer.add_char pad '\n'
        else if Char.code c land 0xC0 <> 0x80 then Buffer.add_char pad ' ')
    src;
  Buffer.contents pad ^ String.sub src start (stop - start)

(* The contract of the item that ends at [stop]: the first comment [(*@ ... *)]
   between [stop] and [next]. *)
let spec src comments stop next =
  match
    List.find_opt
      (fun (s, (l : Location.t)) ->
        String.length s > 0
        && s.[0] = '@'
        && l.loc_start.pos_cnum >= stop
        && l.loc_start.pos_cnum < next)
      comments
  with
  | Some (_, l) -> Some (comment_text src l)
  | None -> None

(* The top-level items for [si], whose contract is before [next]. *)
let item src comments next (si : structure_item) =
  let spec () = spec src comments si.str_loc.loc_end.pos_cnum next in
  match si.str_desc with
  | Tstr_eval (e, _) -> [ Expr_item (expr e) ]
  | Tstr_value (Nonrecursive, [ vb ]) -> (
      match simple_name vb.vb_pat with
      (* [let _ = e] and [let () = e] define no name: they are the expression [e] *)
      | Some "_" -> [ Expr_item (expr vb.vb_expr) ]
      | Some x -> [ Let_item (x, expr vb.vb_expr, spec ()) ]
      | None ->
          (* [let p = e]: [e] is named [v], then each name of [p] is defined by a test
             of [p] on [v] *)
          let v = fresh () in
          let loc = vb.vb_loc in
          let test ok = pattern vb.vb_pat v ok (match_failure loc) in
          Let_item (v, expr vb.vb_expr, None)
          ::
          (match pat_bound_idents vb.vb_pat with
          | [] -> [ Expr_item (test (unit loc)) ]
          | ids ->
              List.map
                (fun id ->
                  Let_item (Ident.name id, test (var loc (Ident.name id)), None))
                ids))
  | Tstr_value (Recursive, [ vb ]) ->
      let f, x, b = rec_fun vb in
      [ Letrec_item (f, x, b, spec ()) ]
  | Tstr_value _ -> unsupported si.str_loc "`let ... and ...`"
  (* a constructor of a type is rejected where it is used *)
  | Tstr_exception _ | Tstr_type _ | Tstr_attribute _ -> []
  | _ -> unsupported si.str_loc "this declaration"

let program src comments (str : structure) =
  let rec go = function
    | [] -> []
    | si :: rest ->
        let next =
          match rest with
          | n :: _ -> n.str_loc.loc_start.pos_cnum
          | [] -> max_int
        in
        let items = item src comments next si in
        items @ go rest
  in
  let buf = Buffer.create 4096 in
  Buffer.add_string buf "(program";
  List.iter
    (fun x ->
      Buffer.add_string buf "\n  ";
      print buf (item_to_sexp x))
    (go str.str_items);
  Buffer.add_string buf ")\n";
  Buffer.contents buf

let () =
  if Array.length Sys.argv <> 2 then begin
    prerr_endline "usage: ocaml-frontend FILE.ml";
    exit 2
  end;
  let file = Sys.argv.(1) in
  Compmisc.init_path ();
  Location.input_name := file;
  let env = Compmisc.initial_env () in
  match
    let ast = Pparse.parse_implementation ~tool_name:"ocaml-frontend" file in
    let comments = Lexer.comments () in
    let str, _, _, _, _ = Typemod.type_structure env ast in
    (str, comments)
  with
  | exception e ->
      Location.report_exception Format.err_formatter e;
      exit 2
  | str, comments -> (
      let src = In_channel.with_open_bin file In_channel.input_all in
      match program src comments str with
      | out -> print_string out
      | exception Unsupported (loc, msg) ->
          Location.print_report Format.err_formatter
            (Location.errorf ~loc "DIVA doesn't support %s" msg);
          exit 1)
