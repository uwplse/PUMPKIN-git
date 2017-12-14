(*
 * Git utilities
 *)

val stash : unit -> unit
val stash_pop : unit -> unit
val checkout : string -> unit

(*
 * Get the root directory of the local git repository
 *)
val git_root : unit -> unit

(*
 * Get the path to a file relative to the git repository's root directory
 *)
val git_path : string -> string
