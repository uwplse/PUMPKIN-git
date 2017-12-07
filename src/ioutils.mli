(* --- Utilities for IO --- *)

(* Read an input channel into a list of strings *)
val slurp : in_channel -> string list

(* Output a string with a newline to an output channel *)
val output_line : out_channel -> string -> unit

(* Output a list of strings with newlines to an output channel *)
val output_lines : out_channel -> string list -> unit

