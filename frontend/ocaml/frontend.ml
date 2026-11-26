(* The OCaml front end of DIVA (untrusted).

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

(* ---------- S-expressions ---------- *)

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

(* The expression [(KIND START STOP args...)], for the part [loc] of the file. *)
let node (loc : Location.t) kind args =
  List
    (Atom kind
    :: Atom (string_of_int loc.loc_start.pos_cnum)
    :: Atom (string_of_int loc.loc_end.pos_cnum)
    :: args)

let var loc x = node loc "var" [ Str x ]
let int loc n = node loc "int" [ Atom (string_of_int n) ]
let bool loc b = node loc "bool" [ Atom (string_of_bool b) ]
let unit loc = node loc "unit" []
let letin loc x a b = node loc "letin" [ Str x; a; b ]
let seq loc a b = letin loc "_" a b
let ite loc c t e = node loc "ite" [ c; t; e ]
let binop loc op a b = node loc "binop" [ Atom op; a; b ]
let app loc f a = node loc "app" [ f; a ]

(* [s], an integer of [bits] bits: DIVA checks that its value fits, if it may not
   ([Overflow.wrap] in [Diva/Sexp.lean]). *)
let overflow loc bits s = node loc "overflow" [ Atom (string_of_int bits); s ]

(* [a op b] on integers of [bits] bits. *)
let arith loc bits op a b = overflow loc bits (binop loc op a b)

(* A new name. Names that start with [%] can't be written in OCaml, so they hide no
   name of the program. *)
let fresh =
  let n = ref 0 in
  fun () ->
    incr n;
    Printf.sprintf "%%t%d" !n

(* ---------- Types ---------- *)

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

(* ---------- Expressions ---------- *)

(* The operators of DIVA. DIVA's [=] and [<>] work on integers, booleans and [()], and
   its other comparisons only on integers. On other values, they stop the program with a
   type error. So a comparison on another type is rejected: it would always fail. On a
   type variable ['a], it is accepted: DIVA's result is OCaml's, or a failure that DIVA
   reports. *)
let binops =
  [
    ("Stdlib.+", "add");
    ("Stdlib.-", "sub");
    ("Stdlib.*", "mul");
    ("Stdlib./", "div");
    ("Stdlib.mod", "mod");
    ("Stdlib.=", "eq");
    ("Stdlib.<>", "ne");
    ("Stdlib.<", "lt");
    ("Stdlib.<=", "le");
    ("Stdlib.>", "gt");
    ("Stdlib.>=", "ge");
  ]

(* The integer constants of the library. *)
let constants =
  [
    ("Stdlib.max_int", string_of_int max_int);
    ("Stdlib.min_int", string_of_int min_int);
    ("Stdlib.Int32.zero", "0");
    ("Stdlib.Int32.one", "1");
    ("Stdlib.Int32.minus_one", "-1");
    ("Stdlib.Int32.max_int", Int32.to_string Int32.max_int);
    ("Stdlib.Int32.min_int", Int32.to_string Int32.min_int);
    ("Stdlib.Int64.zero", "0");
    ("Stdlib.Int64.one", "1");
    ("Stdlib.Int64.minus_one", "-1");
    ("Stdlib.Int64.max_int", Int64.to_string Int64.max_int);
    ("Stdlib.Int64.min_int", Int64.to_string Int64.min_int);
  ]

(* The modules of integers with a fixed number of bits other than [int]'s 63, and
   their functions: [Int32.add], ... *)
let int_modules = [ ("Stdlib.Int32.", 32); ("Stdlib.Int64.", 64) ]

let int_functions =
  [
    ("add", "add");
    ("sub", "sub");
    ("mul", "mul");
    ("div", "div");
    ("rem", "mod");
  ]

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

(* The name of the library function [f], if [f] is one, such as [Stdlib.+]. *)
let library f =
  match f.exp_desc with
  | Texp_ident ((Path.Pdot _ as p), _, _) -> Some (Path.name p)
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
  | Texp_apply (f, args) -> (
      match library f with
      | Some p when List.mem p total ->
          List.for_all
            (function Asttypes.Nolabel, Arg a -> trivial a | _ -> false)
            args
      | _ -> false)
  | _ -> false

(* The name bound by the pattern [p]: a name, [_] or [()]. *)
let pat_name (p : pattern) =
  match p.pat_desc with
  | Tpat_var (id, _, _) -> Ident.name id
  (* [(x : t)] is [(_ : t) as x] *)
  | Tpat_alias ({ pat_desc = Tpat_any; _ }, id, _, _, _) -> Ident.name id
  | Tpat_any -> "_"
  | Tpat_construct (_, cd, [], _) when cd.cstr_name = "()" -> "_"
  | _ -> unsupported p.pat_loc "this pattern (only a name, `_` or `()` for now)"

let is_exception (cd : Data_types.constructor_description) =
  match cd.cstr_tag with Cstr_extension _ -> true | _ -> false

(* The translation of [e]. The sub-expressions are translated from the first to the
   last, with [let]: OCaml computes the arguments of a function from the last to the
   first. So the first construct that isn't supported is the one reported. *)
let rec expr (e : expression) : sexp =
  let loc = e.exp_loc in
  match e.exp_desc with
  | Texp_ident (Path.Pident id, _, _) -> var loc (Ident.name id)
  | Texp_ident (p, _, _) when List.mem_assoc (Path.name p) constants ->
      node loc "int" [ Atom (List.assoc (Path.name p) constants) ]
  | Texp_ident (p, _, _) ->
      unsupported loc "the library function `%s`, except when it is called"
        (Path.name p)
  | Texp_constant (Const_int n) -> int loc n
  | Texp_constant (Const_int32 n) -> node loc "int" [ Atom (Int32.to_string n) ]
  | Texp_constant (Const_int64 n) -> node loc "int" [ Atom (Int64.to_string n) ]
  | Texp_constant (Const_char c) -> int loc (Char.code c)
  | Texp_constant _ ->
      unsupported loc "this constant (only integers and characters)"
  | Texp_construct (_, cd, args) -> construct loc cd args
  | Texp_let (Nonrecursive, [ vb ], body) ->
      let x = pat_name vb.vb_pat in
      let a = expr vb.vb_expr in
      letin loc x a (expr body)
  | Texp_let (Recursive, [ vb ], body) ->
      let f, x, b = rec_fun vb in
      node loc "letrec" [ Str f; Str x; b; expr body ]
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
  | Texp_assert (c, _) -> node loc "assert" [ expr c ]
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
      node loc "tryw" [ a; Str k; handlers loc (var loc k) cases (Some k) ]
  | Texp_while (c, b) ->
      (* as DIVA's parser: [let rec %while _ = if c then (b; %while ()) else () in
       %while ()] *)
      let c = expr c in
      let next = app loc (var loc "%while") (unit loc) in
      node loc "letrec"
        [
          Str "%while";
          Str "_";
          ite loc c (seq loc (expr b) next) (unit loc);
          next;
        ]
  | Texp_for (id, _, lo, hi, dir, b) ->
      (* as DIVA's parser: [let %lo = lo in let %hi = hi in
       let rec %for i = if i <= %hi then (b; %for (i + 1)) else () in %for %lo] *)
      let i = Ident.name id in
      let lo = expr lo in
      let hi = expr hi in
      let cmp, step =
        match dir with Upto -> ("le", "add") | Downto -> ("ge", "sub")
      in
      let next =
        app loc (var loc "%for") (binop loc step (var loc i) (int loc 1))
      in
      let loop =
        node loc "letrec"
          [
            Str "%for";
            Str i;
            ite loc
              (binop loc cmp (var loc i) (var loc "%hi"))
              (seq loc (expr b) next)
              (unit loc);
            app loc (var loc "%for") (var loc "%lo");
          ]
      in
      letin loc "%lo" lo (letin loc "%hi" hi loop)
  | Texp_tuple _ -> unsupported loc "tuples (for now)"
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
  | "[]", [] -> node loc "nil" []
  | "::", [ a; b ] -> ordered loc [ a; b ] (fun l -> node loc "cons" l)
  | c, [] when is_exception cd -> node loc "exn" [ Str c; unit loc ]
  | c, [ a ] when is_exception cd -> node loc "exn" [ Str c; arg a ]
  | c, _ ->
      unsupported loc
        "the constructor `%s` (only exceptions with at most one argument)" c

(* An argument of an exception or of an output function. A string is [()]: DIVA has
   no strings. *)
and arg a =
  match a.exp_desc with
  | Texp_constant (Const_string _) -> unit a.exp_loc
  | _ -> expr a

(* [fun x1 -> ... -> body]. [function cases] adds a parameter, matched by the cases. *)
and lams loc params body =
  match params with
  | p :: ps ->
      let x =
        match (p.fp_arg_label, p.fp_kind) with
        | Nolabel, Tparam_pat pat -> pat_name pat
        | _ -> unsupported p.fp_loc "labelled and optional parameters"
      in
      node loc "lam" [ Str x; lams loc ps body ]
  | [] -> (
      match body with
      | Tfunction_body b -> expr b
      | Tfunction_cases { cases; loc = cloc; _ } ->
          let x = fresh () in
          node loc "lam" [ Str x; match_cases cloc (var cloc x) cases ])

(* [let rec f x = b]: the name of the function, its first parameter, and the rest. *)
and rec_fun vb =
  let f = pat_name vb.vb_pat in
  match vb.vb_expr.exp_desc with
  | Texp_function _ -> (
      match expr vb.vb_expr with
      | List [ Atom "lam"; _; _; Str x; b ] -> (f, x, b)
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
      | _, (`Int | `Var) | ("eq" | "ne"), (`Bool | `Unit) -> ()
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
      overflow loc 63 (binop loc "sub" (int loc 0) (expr a))
  | Some "Stdlib.ref", [ v ] -> node loc "ref" [ expr v ]
  | Some "Stdlib.!", [ r ] -> node loc "deref" [ expr r ]
  | Some "Stdlib.:=", [ r; v ] ->
      two r v (fun r v -> node loc "assign" [ r; v ])
  | Some (("Stdlib.incr" | "Stdlib.decr") as p), [ r ] ->
      let op = if p = "Stdlib.incr" then "add" else "sub" in
      with_name loc r (fun r ->
          node loc "assign"
            [
              r;
              overflow loc 63
                (binop loc op (node loc "deref" [ r ]) (int loc 1));
            ])
  | Some "Stdlib.raise", [ v ] -> node loc "raise" [ expr v ]
  | Some "Stdlib.failwith", [ s ] ->
      node loc "raise" [ node loc "exn" [ Str "Failure"; arg s ] ]
  | Some "Stdlib.invalid_arg", [ s ] ->
      node loc "raise" [ node loc "exn" [ Str "Invalid_argument"; arg s ] ]
  | Some "Stdlib.ignore", [ a ] -> seq loc (expr a) (unit loc)
  | Some p, [ a ] when List.mem p output_functions -> seq loc (arg a) (unit loc)
  | Some "Stdlib.Char.code", [ a ] -> expr a
  | Some p, _ when Option.is_some (int_module p) -> (
      let bits, name = Option.get (int_module p) in
      match (name, args) with
      | n, [ a; b ] when List.mem_assoc n int_functions ->
          two a b (fun a b -> arith loc bits (List.assoc n int_functions) a b)
      | "neg", [ a ] -> overflow loc bits (binop loc "sub" (int loc 0) (expr a))
      (* [Int32.of_int] wraps an [int] that doesn't fit in 32 bits *)
      | "of_int", [ a ] ->
          if bits < 63 then overflow loc bits (expr a) else expr a
      (* [Int64.to_int] wraps an [Int64.t] that doesn't fit in 63 bits *)
      | "to_int", [ a ] ->
          if bits > 63 then overflow loc 63 (expr a) else expr a
      | _ -> unsupported loc "the library function `%s`" p)
  | Some "Stdlib.Array.make", [ n; v ] ->
      two n v (fun n v -> node loc "alloc" [ n; v ])
  | Some "Stdlib.Array.length", [ a ] -> node loc "len" [ expr a ]
  | Some "Stdlib.Array.get", [ a; i ] ->
      two a i (fun a i -> node loc "get" [ a; i ])
  | Some "Stdlib.Array.set", [ a; i; v ] ->
      ordered loc [ a; i; v ] (function
        | [ a; i; v ] -> node loc "set" [ a; i; v ]
        | _ -> assert false)
  | Some p, _ -> unsupported loc "the library function `%s`" p
  | None, _ ->
      ordered loc (f :: args) (function
        | f :: args -> List.fold_left (app loc) f args
        | [] -> assert false)

(* [match s with cases]. *)
and match_ loc s cases =
  (* the handlers of an exception use it several times *)
  if is_exn_type s && not (trivial s) then
    let x = fresh () in
    letin loc x (expr s) (match_cases loc (var loc x) cases)
  else match_cases loc (expr s) cases

and is_exn_type s =
  match Types.get_desc (Ctype.expand_head s.exp_env s.exp_type) with
  | Tconstr (p, [], _) -> Path.same p Predef.path_exn
  | _ -> false

(* The cases of a [match] on [s], which has been translated: [[] -> n | x :: xs -> c]
   (in any order), or exceptions [E x -> h | ... | _ -> m]. *)
and match_cases loc s cases =
  List.iter
    (fun c ->
      if c.c_guard <> None then unsupported c.c_lhs.pat_loc "`when` (for now)")
    cases;
  let ctor (c : value case) =
    match c.c_lhs.pat_desc with
    | Tpat_construct (_, cd, ps, _) -> Some (cd.cstr_name, ps)
    | _ -> None
  in
  match cases with
  | [ c1; c2 ]
    when match (ctor c1, ctor c2) with
         | Some ("[]", _), Some ("::", _) | Some ("::", _), Some ("[]", _) ->
             true
         | _ -> false -> (
      let nil, cons =
        match ctor c1 with Some ("[]", _) -> (c1, c2) | _ -> (c2, c1)
      in
      match ctor cons with
      | Some (_, [ x; xs ]) ->
          let n = expr nil.c_rhs in
          node loc "matchList"
            [ s; n; Str (pat_name x); Str (pat_name xs); expr cons.c_rhs ]
      | _ -> assert false)
  | _ ->
      let exn_case (c : value case) =
        match c.c_lhs.pat_desc with
        | Tpat_construct (_, cd, _, _) -> is_exception cd
        | Tpat_any | Tpat_var _ -> true
        | _ -> false
      in
      if List.for_all exn_case cases then handlers loc s cases None
      else
        unsupported loc
          "this `match` (only `[] -> ... | x :: xs -> ...` and exceptions, for \
           now)"

(* The handlers [cases] of an exception [s]: [E x -> h | ... | k -> m]. An exception
   that no handler matches is raised again, if [reraise] is its name (in [try]).
   Otherwise the cases must match every exception. *)
and handlers loc s cases reraise =
  match cases with
  | [] -> (
      match reraise with
      | Some k -> node loc "raise" [ var loc k ]
      | None ->
          unsupported loc "a `match` on an exception without a last case `_`")
  | c :: rest -> (
      if c.c_guard <> None then unsupported c.c_lhs.pat_loc "`when` (for now)";
      match c.c_lhs.pat_desc with
      | Tpat_construct (_, cd, ps, _) when is_exception cd ->
          let x =
            match ps with
            | [] -> "_"
            | [ p ] -> pat_name p
            | _ ->
                unsupported c.c_lhs.pat_loc
                  "an exception with several arguments"
          in
          let h = expr c.c_rhs in
          node loc "exnCase"
            [ s; Str cd.cstr_name; Str x; h; handlers loc s rest reraise ]
      | Tpat_any -> expr c.c_rhs
      | Tpat_var (id, _, _) -> letin loc (Ident.name id) s (expr c.c_rhs)
      | _ ->
          unsupported c.c_lhs.pat_loc
            "this pattern (only an exception, a name or `_`)")

(* ---------- Top-level items ---------- *)

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
  | Some (_, l) -> [ Str (comment_text src l) ]
  | None -> []

(* The top-level item [si], whose contract is before [next]. *)
let item src comments next (si : structure_item) =
  let spec () = spec src comments si.str_loc.loc_end.pos_cnum next in
  match si.str_desc with
  | Tstr_eval (e, _) -> Some (List [ Atom "expr"; expr e ])
  (* [let _ = e] and [let () = e] define no name: they are the expression [e] *)
  | Tstr_value (Nonrecursive, [ vb ]) when pat_name vb.vb_pat = "_" ->
      Some (List [ Atom "expr"; expr vb.vb_expr ])
  | Tstr_value (Nonrecursive, [ vb ]) ->
      Some
        (List
           ([ Atom "let"; Str (pat_name vb.vb_pat); expr vb.vb_expr ] @ spec ()))
  | Tstr_value (Recursive, [ vb ]) ->
      let f, x, b = rec_fun vb in
      Some (List ([ Atom "letrec"; Str f; Str x; b ] @ spec ()))
  | Tstr_value _ -> unsupported si.str_loc "`let ... and ...`"
  (* a constructor of a type is rejected where it is used *)
  | Tstr_exception _ | Tstr_type _ | Tstr_attribute _ -> None
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
        let x = item src comments next si in
        Option.to_list x @ go rest
  in
  let buf = Buffer.create 4096 in
  Buffer.add_string buf "(program";
  List.iter
    (fun x ->
      Buffer.add_string buf "\n  ";
      print buf x)
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
