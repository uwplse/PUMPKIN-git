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

(* Copy input_file to output_file, writing text at the supplied line *)
let splice input_filename output_filename line text : unit =
  let pos = ref 0 in
  let input = open_in input_filename in
  let output = open_out output_filename in
  try
    while true do
      let buffer = input_line input in
      pos := !pos + 1;
      if line = !pos then
        (output_lines output text;
         output_char output '\n');
      output_line output buffer
    done
  with End_of_file ->
    if !pos < line then
      (output_lines output text;
       output_char output '\n');
    flush output;
    close_in input;
    close_out output
