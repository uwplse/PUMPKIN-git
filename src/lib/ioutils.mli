(* --- Utilities for IO --- *)

(* Read an input channel into a list of strings *)
val slurp : in_channel -> string list

(* Output a string with a newline to an output channel *)
val output_line : out_channel -> string -> unit

(* Output a list of strings with newlines to an output channel *)
val output_lines : out_channel -> string list -> unit

(*
 * Given an input file name, output file name, line number, and text,
 * copy the text from input to output, writing text at the specified line.
 *
 * If the line number is greater than the number of lines in the file,
 * then this writes at the end of the file.
 *)
val splice : string -> string -> int -> string list -> unit
