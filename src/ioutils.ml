(* --- Utilities for IO --- *)

(* Convert input from a channel into a list of strings *)
let slurp ch : string list =
  let buf = ref [] in
  try
    while true do
      buf := input_line ch :: !buf
    done;
    !buf
  with End_of_file ->
    close_in ch;
    List.rev !buf

(* Output a string with a newline to an output channel *)
let output_line ch s =
  output_string ch s;
  output_char ch '\n'

(* Output a list of strings with newlines to an output channel *)
let output_lines ch = List.iter (output_line ch)
