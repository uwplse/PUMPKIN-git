(* --- Processing PUMPKIN Outputs --- *)

type processor

(* Execute a processor *)
val process_using : processor -> unit

(* Chain two processors *)
val chain_processors : processor -> processor -> processor

(* --- Built-in Processors --- *)

(* Do nothing *)
val do_not_process : processor

(*
 * Given the name of a file, produce a processor that calls Coq on
 * that file and outputs the result to stdout
 *)
val call_coq_output : string -> processor

(*
 * Given the name of an input file and the name of an output file,
 * produce a processor that calls Coq on the output file,
 * parses the output to produce a patch, then copies the input
 * file to the output file and updates it to contain the patch.
 *
 * If the boolean is true, add the result to a hint database.
 *
 * The line number tells PUMPKIN at which line to write the patch.
 *)
val call_coq_define : string -> string -> bool -> int -> processor

(*
 * Given the name of an input file and the name of an output file,
 * produce a processor that calls Coq on the output file,
 * parses the output to produce a patch, copies the input
 * file to the output file and updates it to contain the patch,
 * then prompts the user for whether or not to overwrite the input file
 * with the output file.
 *
 * If the boolean is true, add the result to a hint database.
 *
 * The line number tells PUMPKIN at which line to write the patch.
 *)
val call_coq_prompt : string -> string -> bool -> int -> processor

(*
 * Given the name of an input file and the name of an output file,
 * produce a processor that calls Coq on the output file,
 * parses the output to produce a patch, copies the input
 * file to the output file and updates it to contain the patch,
 * then overwrites the input file with the output file.
 *
 * If the boolean is true, add the result to a hint database.
 *
 * The line number tells PUMPKIN at which line to write the patch.
 *)
val call_coq_overwrite : string -> string -> bool -> int -> processor
