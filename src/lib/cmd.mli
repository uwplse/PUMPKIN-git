(*
 * Utilities for command-line processes
 *)

(*
 * Try to execute the command (first argument)
 * Take a list of arguments (second argument)
 * Fail with the supplied message if the status is anything other than 0
 *)
val try_execute : string -> string list -> string -> unit

