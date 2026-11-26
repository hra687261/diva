(* An exception that isn't caught is reported at the top-level item that raises it. *)

exception Neg of int

let check x = if x < 0 then raise (Neg x) else x

let safe = try check (-1) with Neg n -> n

(* `Neg` isn't caught here *)
let bad = check (-2)

(* `Not_found` is raised, but only `Neg` is caught *)
let wrong = try raise Not_found with Neg n -> n
