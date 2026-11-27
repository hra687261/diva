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

   The library functions that the program uses and that DIVA doesn't have are written in
   OCaml, in the prelude ([prelude.ml]). The frontend translates the prelude, and adds the
   functions of the prelude that the program uses before the program.

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

(* A function of the prelude. *)
type prelude_fn = {
  id : Ident.t;  (** its name in the prelude's code *)
  name : string;
      (** its name in DIVA: the name of the library function it replaces, such
          as [Stdlib.List.length] *)
  item : item;
  deps : prelude_fn list;  (** the functions of the prelude that it uses *)
  inline : (string list * expr) option;
      (** [[@diva.inline]]: its parameters and its body, copied at each call *)
}
(* TODO: a smarter data structure to represent the prelude functions it uses *)

(* A library function that the translation knows. *)
type library_fn =
  | Op of op  (** [+], [=], ... *)
  | Const of int64  (** [max_int], [Int32.zero], ... *)
  | And
  | Or
  | Not
  | Neg  (** [~-] *)
  | Ref
  | Deref
  | Assign
  | Incr
  | Decr
  | Raise
  | Failwith
  | Invalid_arg
  | Ignore
  | Output
      (** [print_int], ...: DIVA computes the argument and prints nothing *)
  | Char_code
  | Int_op of int * op
      (** [Int32.add], ...: an operation on integers of [bits] bits *)
  | Int_neg of int
  | Of_int of int
      (** [Int32.of_int]: from an [int] to integers of [bits] bits *)
  | To_int of int
      (** [Int64.to_int]: from integers of [bits] bits to an [int] *)
  | Array_make
  | Array_length
  | Array_get
  | Array_set
  | Prelude of prelude_fn

(**** State ****)

(* The mutable values of the translation. *)

(* The code being translated is the prelude, which isn't in the file. *)
let in_prelude = ref false

(* The library functions that the translation knows, by their path. The functions of
   the prelude are added when the prelude is translated. *)
let library_paths : library_fn Path.Map.t ref = ref Path.Map.empty

(* The functions of the prelude translated so far, by their [Ident.t]. *)
let prelude_fns : prelude_fn Ident.Tbl.t = Ident.Tbl.create 64

(* The DIVA names of the functions of the prelude, by their [Ident.t]. A function's name
   is recorded before its code is translated: a recursive function uses its own name. *)
let prelude_names : string Ident.Tbl.t = Ident.Tbl.create 64

(* The modules of the prelude, such as [List], with their functions. *)
let prelude_modules : prelude_fn list Ident.Tbl.t = Ident.Tbl.create 4

(* The functions of the prelude that the code translated so far uses. *)
let used : prelude_fn list ref = ref []

(* The constructors seen so far, by name: an exception or the type of the variant. *)
let ctors : (string, string) Hashtbl.t = Hashtbl.create 16

(* TODO: maybe use a record to represent the state *)

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

(* [e] as [(KIND START STOP args...)], for its part of the file. Code of the prelude has
   no location ([Location.none]) and gets the span [1 0], which DIVA reads as "not in
   the file" ([Span.prelude]). *)
let rec to_sexp (e : expr) =
  let start, stop =
    if e.loc = Location.none then (1, 0)
    else (e.loc.loc_start.pos_cnum, e.loc.loc_end.pos_cnum)
  in
  let node kind args =
    List
      (Atom kind
      :: Atom (string_of_int start)
      :: Atom (string_of_int stop)
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

(* The expression [desc], from the part [loc] of the file. Code of the prelude gets no
   location. *)
let mk loc desc = { loc = (if !in_prelude then Location.none else loc); desc }
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
   name of the program. The new names of the prelude's code are [%pN], and those of the
   program are [%tN]. So the copies of the prelude's code in the program
   ([[@diva.inline]]) hide no new name of the program. *)
let fresh =
  let t = ref 0 in
  let p = ref 0 in
  fun () ->
    let n = if !in_prelude then p else t in
    incr n;
    Printf.sprintf (if !in_prelude then "%%p%d" else "%%t%d") !n

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

(**** Library functions ****)

(* The library functions that the translation knows, other than the functions of the
   prelude, by their names in [Stdlib]. DIVA's [=] and [<>] work on integers, booleans
   and [()], and its other comparisons only on integers. *)
let library_names =
  let int_module (m, bits, min, max) =
    [
      (m ^ ".add", Int_op (bits, Add));
      (m ^ ".sub", Int_op (bits, Sub));
      (m ^ ".mul", Int_op (bits, Mul));
      (m ^ ".div", Int_op (bits, Div));
      (m ^ ".rem", Int_op (bits, Mod));
      (m ^ ".neg", Int_neg bits);
      (m ^ ".of_int", Of_int bits);
      (m ^ ".to_int", To_int bits);
      (m ^ ".zero", Const 0L);
      (m ^ ".one", Const 1L);
      (m ^ ".minus_one", Const (-1L));
      (m ^ ".max_int", Const max);
      (m ^ ".min_int", Const min);
    ]
  in
  [
    ("+", Op Add);
    ("-", Op Sub);
    ("*", Op Mul);
    ("/", Op Div);
    ("mod", Op Mod);
    ("=", Op Eq);
    ("<>", Op Ne);
    ("<", Op Lt);
    ("<=", Op Le);
    (">", Op Gt);
    (">=", Op Ge);
    ("max_int", Const (Int64.of_int max_int));
    ("min_int", Const (Int64.of_int min_int));
    ("&&", And);
    ("||", Or);
    ("not", Not);
    ("~-", Neg);
    ("ref", Ref);
    ("!", Deref);
    (":=", Assign);
    ("incr", Incr);
    ("decr", Decr);
    ("raise", Raise);
    ("failwith", Failwith);
    ("invalid_arg", Invalid_arg);
    ("ignore", Ignore);
    ("print_int", Output);
    ("print_string", Output);
    ("print_endline", Output);
    ("print_newline", Output);
    ("print_char", Output);
    ("Char.code", Char_code);
    ("Array.make", Array_make);
    ("Array.length", Array_length);
    ("Array.get", Array_get);
    ("Array.set", Array_set);
  ]
  @ int_module
      ("Int32", 32, Int64.of_int32 Int32.min_int, Int64.of_int32 Int32.max_int)
  @ int_module ("Int64", 64, Int64.min_int, Int64.max_int)

(* The path of the value [Stdlib.parts] in [env], if there is one. *)
let stdlib_path env parts =
  match Longident.unflatten ("Stdlib" :: parts) with
  | Some lid -> (
      match Env.find_value_by_name lid env with
      | p, _ -> Some p
      | exception Not_found -> None)
  | None -> None

(* Fill [library_paths] with [library_names]. *)
let init_library env =
  List.iter
    (fun (name, f) ->
      match stdlib_path env (String.split_on_char '.' name) with
      | Some p -> library_paths := Path.Map.add p f !library_paths
      | None -> failwith ("no library function Stdlib." ^ name))
    library_names

(* The name of [p], such as [Stdlib.mod], from its parts. [Path.name] writes a keyword
   used as a name after [\#]: [Stdlib.\#mod]. *)
let path_name p =
  match Path.flatten p with
  | `Ok (id, parts) -> String.concat "." (Ident.name id :: parts)
  | `Contains_apply -> Path.name p

(**** The prelude ****)

(* A function of the prelude has the name of the library function it replaces:
   [Stdlib.List.length]. The program can't define such a name, so it hides no function
   of the prelude. *)

(* The name of [id] in DIVA: its name in [prelude_names], or its name in OCaml. *)
let local_name id =
  match Ident.Tbl.find_opt prelude_names id with
  | Some n -> n
  | None -> Ident.name id

(* The library function [p], if the translation knows it. In the prelude's code, a
   function of a module [M] of the prelude is [M.f]: a [Path.Pdot] on [M], with the name
   [f]. *)
let known p =
  match p with
  | Path.Pident id ->
      Option.map (fun f -> Prelude f) (Ident.Tbl.find_opt prelude_fns id)
  | Path.Pdot (Path.Pident m, x) when Ident.Tbl.mem prelude_modules m ->
      List.find_opt
        (fun f -> Ident.name f.id = x)
        (Ident.Tbl.find prelude_modules m)
      |> Option.map (fun f -> Prelude f)
  | p -> Path.Map.find_opt p !library_paths

(* The name of [f], recorded in [used]. *)
let use f =
  if not (List.memq f !used) then used := f :: !used;
  f.name

(* The expression or the binding has the attribute [[@name]]. *)
let has_attribute name (attrs : Parsetree.attributes) =
  List.exists (fun (a : Parsetree.attribute) -> a.attr_name.txt = name) attrs

(* The library function [f], if [f] is one that the translation knows. *)
let library f =
  match f.exp_desc with Texp_ident (p, _, _) -> known p | _ -> None

(* [e] is computed without any effect: no error but an overflow, no read or change of
   the store, and it finishes. So it can be computed earlier or later: if two parts
   overflow, both orders give the same error. In a program that DIVA proves never
   fails, nothing overflows. [+], [-], [*] and [~-] can fail only by overflow, which is
   a failed check, a fatal error. [/] and [mod] also fail on [0]. *)
let rec trivial e =
  match e.exp_desc with
  | Texp_ident (Path.Pident _, _, _) | Texp_constant _ | Texp_function _ -> true
  | Texp_ident (p, _, _) -> (
      match known p with Some (Prelude _) -> true | _ -> false)
  | Texp_construct (_, _, args) -> List.for_all trivial args
  | Texp_tuple es -> List.for_all (fun (_, e) -> trivial e) es
  | Texp_apply (f, args) -> (
      match library f with
      | Some (Op (Add | Sub | Mul) | Neg) ->
          List.for_all
            (function Asttypes.Nolabel, Arg a -> trivial a | _ -> false)
            args
      | _ -> false)
  | _ -> false

(**** Expressions ****)

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
   [Ctor ("C", (a, b))]. A tuple [(a, b)] is [Ctor ("%2", [a; b])]: DIVA's analysis describes each of its
   components. *)

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

(* [e] is a constant, a name, or a constructor or a [raise] of such code: code that is
   copied, rather than put in a function. *)
let rec small_code e =
  match e.desc with
  | Int _ | Bool _ | Unit | Nil | Var _ -> true
  | Ctor (_, v) | Raise v -> small_code v
  | _ -> false

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
  | Texp_ident (p, _, _) -> (
      match (p, known p) with
      | _, Some (Prelude f) -> var loc (use f)
      | Path.Pident id, _ -> var loc (local_name id)
      (* an operator that isn't called, such as [( + )]: [fun a -> fun b -> a + b] *)
      | _, Some (Op op) ->
          let a = fresh () and b = fresh () in
          mk loc
            (Lam (a, mk loc (Lam (b, arith loc 63 op (var loc a) (var loc b)))))
      | _, Some (Const n) -> mk loc (Int n)
      | _ ->
          unsupported loc "the library function `%s`, except when it is called"
            (path_name p))
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
      (* [[@diva.unchecked]]: no overflow check (in the prelude) *)
      let checked = not (has_attribute "diva.unchecked" e.exp_attributes) in
      apply ~checked loc f (List.map arg args)
  | Texp_ifthenelse (c, t, f) ->
      let c = expr c in
      let t = expr t in
      ite loc c t (match f with Some f -> expr f | None -> unit loc)
  | Texp_sequence (a, b) ->
      let a = expr a in
      seq loc a (expr b)
  | Texp_assert (c, _) -> mk loc (Assert (expr c))
  | Texp_match (s, cases, [], partial) ->
      let value (c : computation case) =
        match split_pattern c.c_lhs with
        | Some p, None -> { c with c_lhs = p }
        | _ -> unsupported c.c_lhs.pat_loc "`exception` patterns"
      in
      match_ ~total:(partial = Total) loc s (List.map value cases)
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
      | Tfunction_cases { cases; loc = cloc; partial; _ } ->
          let x = fresh () in
          mk loc
            (Lam
               ( x,
                 match_cases ~total:(partial = Total) cloc x cases
                   (match_failure cloc) )))

(* [let rec f x = b]: the name of the function, its first parameter, and the rest. *)
and rec_fun vb =
  let f =
    match vb.vb_pat.pat_desc with
    | Tpat_var (id, _, _) -> local_name id
    | _ -> pat_name vb.vb_pat
  in
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

(* The call [f args]. Its operations on integers are checked for overflow if [checked]. *)
and apply ?(checked = true) loc f args =
  let two a b k =
    ordered loc [ a; b ] (function [ a; b ] -> k a b | _ -> assert false)
  in
  let call () =
    ordered loc (f :: args) (function
      | f :: args -> List.fold_left (app loc) f args
      | [] -> assert false)
  in
  (* the name of the library function [f], for the errors *)
  let name () =
    match f.exp_desc with Texp_ident (p, _, _) -> path_name p | _ -> "?"
  in
  match (library f, args) with
  | Some (Op op), [ a; b ] ->
      (* On other values than these, DIVA's operators stop the program with a type
         error, so the operation is rejected: it would always fail. On a type
         variable ['a], it is accepted: DIVA's result is OCaml's, or a failure that
         DIVA reports. *)
      (match (op, kind a.exp_env a.exp_type) with
      | _, (`Int | `Var) | (Eq | Ne), (`Bool | `Unit) -> ()
      | _ -> unsupported loc "`%s` on this type" (name ()));
      two a b (fun a b ->
          if checked then arith loc 63 op a b else binop loc op a b)
  | Some And, [ a; b ] ->
      let a = expr a in
      ite loc a (expr b) (bool loc false)
  | Some Or, [ a; b ] ->
      let a = expr a in
      ite loc a (bool loc true) (expr b)
  | Some Not, [ a ] -> ite loc (expr a) (bool loc false) (bool loc true)
  | Some Neg, [ a ] -> overflow loc 63 (binop loc Sub (int loc 0) (expr a))
  | Some Ref, [ v ] -> mk loc (Ref (expr v))
  | Some Deref, [ r ] -> mk loc (Deref (expr r))
  | Some Assign, [ r; v ] -> two r v (fun r v -> mk loc (Assign (r, v)))
  | Some ((Incr | Decr) as g), [ r ] ->
      let op = if g = Incr then Add else Sub in
      with_name loc r (fun r ->
          mk loc (Assign (r, arith loc 63 op (mk loc (Deref r)) (int loc 1))))
  | Some Raise, [ v ] -> mk loc (Raise (expr v))
  | Some Failwith, [ s ] -> mk loc (Raise (mk loc (Ctor ("Failure", arg s))))
  | Some Invalid_arg, [ s ] ->
      mk loc (Raise (mk loc (Ctor ("Invalid_argument", arg s))))
  | Some Ignore, [ a ] -> seq loc (expr a) (unit loc)
  | Some Output, [ a ] -> seq loc (arg a) (unit loc)
  | Some Char_code, [ a ] -> expr a
  | Some (Int_op (bits, op)), [ a; b ] ->
      two a b (fun a b -> arith loc bits op a b)
  | Some (Int_neg bits), [ a ] ->
      overflow loc bits (binop loc Sub (int loc 0) (expr a))
  (* [Int32.of_int] wraps an [int] that doesn't fit in 32 bits *)
  | Some (Of_int bits), [ a ] ->
      if bits < 63 then overflow loc bits (expr a) else expr a
  (* [Int64.to_int] wraps an [Int64.t] that doesn't fit in 63 bits *)
  | Some (To_int bits), [ a ] ->
      if bits > 63 then overflow loc 63 (expr a) else expr a
  | Some Array_make, [ n; v ] -> two n v (fun n v -> mk loc (Alloc (n, v)))
  | Some Array_length, [ a ] -> mk loc (Len (expr a))
  | Some Array_get, [ a; i ] -> two a i (fun a i -> mk loc (Get (a, i)))
  | Some Array_set, [ a; i; v ] ->
      ordered loc [ a; i; v ] (function
        | [ a; i; v ] -> mk loc (Set (a, i, v))
        | _ -> assert false)
  | Some (Prelude { inline = Some (ps, body); deps; _ }), _
    when List.length ps = List.length args ->
      (* a copy of the code of the function. Each argument gets a new name, and the
         arguments are computed from the last to the first, as in OCaml. Then each
         parameter is defined as its argument. *)
      List.iter (fun g -> ignore (use g)) deps;
      let args = List.map (fun a -> (fresh (), expr a)) args in
      let body =
        List.fold_right2
          (fun p (x, _) b -> letin loc p (var loc x) b)
          ps args body
      in
      List.fold_left (fun b (x, a) -> letin loc x a b) body args
  | Some (Prelude _), _ -> call ()
  (* a known library function with other arguments, or another one *)
  | Some _, _ -> unsupported loc "the library function `%s`" (name ())
  | None, _ -> (
      match f.exp_desc with
      | Texp_ident (Path.Pdot _, _, _) ->
          unsupported loc "the library function `%s`" (name ())
      | _ -> call ())

(* [match s with cases]. *)
and match_ ?(total = false) loc s cases =
  (* the name of [s] in the tests: [s] itself if it is a name that no case hides *)
  let bound =
    List.concat_map
      (fun c -> List.map Ident.name (pat_bound_idents c.c_lhs))
      cases
  in
  match s.exp_desc with
  | Texp_ident (Path.Pident id, _, _) when not (List.mem (Ident.name id) bound)
    ->
      match_cases ~total loc (Ident.name id) cases (match_failure loc)
  | _ ->
      let v = fresh () in
      let s = expr s in
      letin loc v s (match_cases ~total loc v cases (match_failure loc))

(* The cases of a [match] on the name [v]. [final] is what happens if no case matches:
   it is copied, so it must be small. [[] -> n | x :: xs -> c] (in any order) is DIVA's
   [match] on lists. *)
and match_cases ?(total = false) loc v cases final =
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
  | _ -> case_list total loc v cases final

(* The cases, tried one after the other. When a case doesn't match, the next ones are
   tried: they are the code [next], copied if it is [small_code], or else a
   function [%tN] that the case calls. A copy is better for DIVA: the analysis and
   [prove] follow it at the place of the test that failed. If OCaml says that the cases match every value ([total]), the last
   case matches when the others don't: if it binds no name, it isn't tested. *)
and case_list total loc v cases final =
  match cases with
  | [] -> final
  | [ c ]
    when total && Option.is_none c.c_guard
         && List.is_empty (pat_bound_idents c.c_lhs) ->
      expr c.c_rhs
  | c :: rest ->
      let next, define =
        if rest = [] then (final, fun e -> e)
        else
          let code = case_list total loc v rest final in
          if uses c <= 1 || small_code code then (code, fun e -> e)
          else
            let k = fresh () in
            let f = mk loc (Lam ("_", code)) in
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
and uses (c : value case) =
  pat_uses c.c_lhs + if Option.is_none c.c_guard then 0 else 1

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

(* a tuple: only its components can fail to match (see [tuple_pattern]) *)
and tuple_uses ps = List.fold_left (fun n p -> n + pat_uses p) 0 ps

(* The test of the pattern [p] on the value of the name [v]: [ok] if it matches, with the
   names of [p] bound, else [ko]. [ko] is copied: it must be small. Its names are names
   that start with [%]: [p] doesn't hide them. *)
and pattern (p : pattern) v ok ko =
  let loc = p.pat_loc in
  match p.pat_desc with
  | Tpat_any -> ok
  | Tpat_var (id, _, _) when String.equal (Ident.name id) v -> ok
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
          let h = name_for ph in
          let t = name_for pt in
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

(* The test of the tuple pattern [(p1, ..., pn)] on [v]. A value of a tuple type is
   always a tuple of [n] components, so the tests of its constructor and of the length
   of its list never fail: they raise [Match_failure], instead of copying [ko]. *)
and tuple_pattern loc ps v ok ko =
  let bad = match_failure loc in
  let l = fresh () in
  let rec components l = function
    | [] -> ok
    | p :: ps ->
        let h = name_for p in
        let t = if List.is_empty ps then "_" else fresh () in
        mk loc
          (MatchList (var loc l, bad, h, t, pattern p h (components t ps) ko))
  in
  mk loc
    (CtorCase (var loc v, tuple_ctor (List.length ps), l, components l ps, bad))

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
  let start = loc.loc_start.pos_cnum in
  let stop = loc.loc_end.pos_cnum in
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
        && Char.equal s.[0] '@'
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

(* The functions of the prelude [str], in order. [env] is the environment of the
   program: each function that replaces a library function is added to [library_paths],
   with the path of the library function in [env]. *)
let prelude_fns_of env (str : structure) =
  (* [fun x1 -> ... -> fun xn -> body]: the parameters [x1 ... xn] and [body] *)
  let rec params e =
    match e.desc with
    | Lam (x, b) ->
        let xs, body = params b in
        (x :: xs, body)
    | _ -> ([], e)
  in
  (* [path]: the modules of the prelude that contain [str], such as [["List"]] *)
  let rec items path (str : structure) =
    List.concat_map
      (fun si ->
        match si.str_desc with
        | Tstr_value
            ( flag,
              [ ({ vb_pat = { pat_desc = Tpat_var (id, _, _); _ }; _ } as vb) ]
            ) ->
            let parts = path @ [ Ident.name id ] in
            let name = String.concat "." ("Stdlib" :: parts) in
            Ident.Tbl.replace prelude_names id name;
            used := [];
            let item =
              match flag with
              | Nonrecursive -> Let_item (name, expr vb.vb_expr, None)
              | Recursive ->
                  let _, x, b = rec_fun vb in
                  Letrec_item (name, x, b, None)
            in
            let inline =
              if has_attribute "diva.inline" vb.vb_attributes then
                match item with
                | Let_item (_, e, _) -> Some (params e)
                | _ ->
                    failwith "the prelude has a `let rec` with [@diva.inline]"
              else None
            in
            let f = { id; name; item; deps = !used; inline } in
            Ident.Tbl.replace prelude_fns id f;
            (match stdlib_path env parts with
            | Some p ->
                library_paths := Path.Map.add p (Prelude f) !library_paths
            | None -> ());
            [ f ]
        | Tstr_module
            { mb_id = Some m; mb_expr = { mod_desc = Tmod_structure s; _ }; _ }
          ->
            let fs = items (path @ [ Ident.name m ]) s in
            Ident.Tbl.replace prelude_modules m fs;
            fs
        | _ -> failwith "the prelude has only `let`s of names and modules")
      str.str_items
  in
  in_prelude := true;
  let fs = items [] str in
  in_prelude := false;
  fs

(* The items of the functions of the prelude [prelude] that [fs] use, and those that
   these use, in order. *)
let needed prelude fs =
  let rec add need f =
    if List.memq f need then need else List.fold_left add (f :: need) f.deps
  in
  let need = List.fold_left add [] fs in
  List.filter_map
    (fun f -> if List.memq f need then Some f.item else None)
    prelude

let program src comments prelude (str : structure) =
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
  used := [];
  let items = go str.str_items in
  let prelude = needed prelude !used in
  let buf = Buffer.create 4096 in
  Buffer.add_string buf "(program";
  List.iter
    (fun x ->
      Buffer.add_string buf "\n  ";
      print buf (item_to_sexp x))
    (prelude @ items);
  Buffer.add_string buf ")\n";
  Buffer.contents buf

let () =
  if Array.length Sys.argv <> 2 then begin
    prerr_endline "usage: ocaml-frontend FILE.ml";
    exit 2
  end;
  let file = Sys.argv.(1) in
  Compmisc.init_path ();
  let env = Compmisc.initial_env () in
  init_library env;
  (* the prelude, in the same environment as the program: OCaml's standard library *)
  let prelude =
    let lexbuf = Lexing.from_string Prelude_text.text in
    Lexing.set_filename lexbuf "prelude.ml";
    let str, _, _, _, _ =
      Typemod.type_structure env (Parse.implementation lexbuf)
    in
    prelude_fns_of env str
  in
  Location.input_name := file;
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
      match program src comments prelude str with
      | out -> print_string out
      | exception Unsupported (loc, msg) ->
          Location.print_report Format.err_formatter
            (Location.errorf ~loc "DIVA doesn't support %s" msg);
          exit 1)
