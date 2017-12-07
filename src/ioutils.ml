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
