(* --- Outputting Definitions and Dependencies --- *)

(*
 * An outputter takes the text of a definition (as a list of strings)
 * and the text of its dependencies (a list of lists of strings) and
 * outputs it in some way to some channel (for example, to standard out
 * or to a file).
 *)
type outputter

val output_using : outputter -> string list -> string list list -> unit

(* --- Built-in Outputters ---*)

(* Output to stdout *)
val show : outputter

(* Add the definition and its dependencies to a file wrapped in a module *)
val define : string -> string -> string -> int -> outputter

(* Add the definition and its dependencies, then add calls to PUMPKIN *)
val patch : string -> string -> string option -> string -> string -> string -> int -> outputter

