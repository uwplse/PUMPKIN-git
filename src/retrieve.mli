(* --- Retrieve Coq definitions and dependencies from Git --- *)

(*
 * Retrieve definition of an identifier at a particular revision
 * Return a list of strings that correpsonds to that definition
 *)
val retrieve_def : string -> string -> string -> string list
