(*
 * Git utilities
 *)

(* --- Basic git functionality --- *)

(*
 * Stash
 *)
val stash : unit -> unit

(*
 * Pop the stash
 *)
val stash_pop : unit -> unit

(*
 * Checkout a revision
 *)
val checkout : string -> unit

(*
 * Checkout a specific file (first argument) from a revision (second argument)
 *)
val checkout_file : string -> string -> unit

(*
 * Run git diff and parse the result as a list of strings
 *)
val diff : unit -> string list

(* --- Complex sequences of commands --- *)

(*
 * Return a command that runs if and only if a condition is met
 *)
val run_iff : bool -> (unit -> unit) -> (unit -> unit)

(*
 * Check if there are any local uncommitted changes
 *)
val has_uncommitted : unit -> bool

(*
 * Get the root directory of the local git repository
 *)
val git_root : unit -> string

(*
 * Get the path to a file relative to the git repository's root directory
 *)
val git_path : string -> string
