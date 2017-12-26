open Ioutils

(* --- Processing PUMPKIN Outputs --- *)

type processor = unit -> unit

let process_using processor = processor ()

(* Run coq and produce a list of strings *)
let call_coq filename : string list =
  let run_coq = Printf.sprintf "coqc %s" filename in
  Unix.open_process_in run_coq |> slurp

(* Get a patch definition from pretty-printed output *)
let pp_to_def hint pp : string =
  let begin_patch_pat = Str.regexp "BEGIN PATCH .*" in
  let pp =
    List.rev
      (Core.List.take_while
         (List.rev pp)
         (fun s -> not (Str.string_match begin_patch_pat s 0)))
  in
  let comment = "\n(* Auto-generated by PUMPKIN-git *)" in
  let def = String.concat "\n" (comment :: pp) in
  if hint then
    let id = List.hd (List.tl (Str.split (Str.regexp "[ ]+") (List.hd pp))) in
    Printf.sprintf "%s\n\nHint Resolve %s." def id
  else
    def

(* Update a file to contain a patch *)
let define_patch in_filename out_filename hint line input =
  let input_string = String.concat "\n" input in
  let input_split = Str.split (Str.regexp "END PATCH") input_string in
  let defs = List.map (Str.split (Str.regexp "\n")) input_split in
  Printf.printf "%d" (List.length defs);
  let patches = List.map (pp_to_def hint) defs in
  splice in_filename out_filename line patches

(* --- Processors --- *)

(* Do nothing *)
let do_not_process () = ()

(* Chain two processors *)
let chain_processors p1 p2 () = p1 (); p2 (); ()

(* Call Coq on filename and output the result to stdout *)
let call_coq_output filename () =
  call_coq filename |> output_lines stdout

(* Call Coq on out_filename and define the produced patch *)
let call_coq_define in_filename out_filename hint line () =
  call_coq out_filename |> define_patch in_filename out_filename hint line

(* Overwrite input_filename with output_filename *)
let overwrite input_filename output_filename () =
  let rewrite = Printf.sprintf "mv %s %s" output_filename input_filename in
  match Unix.system rewrite with
   | Unix.WEXITED 0 ->
      ()
   | _ ->
      failwith "Cannot overwrite file. Check permissions."

(* Prompt user to overwrite input_filename with output_filename *)
let prompt_overwrite in_filename out_filename () =
  let diff = Printf.sprintf "diff %s %s" in_filename out_filename in
  output_line stdout "pumpkin-git wants to make the following changes:\n";
  Unix.open_process_in diff |> slurp |> output_lines stdout;
  let rec prompt () =
    output_line stdout (Printf.sprintf "\noverwrite %s? [y/n]" in_filename);
    match read_line () with
    | "y" ->
       overwrite in_filename out_filename ()
    | "n" ->
       ()
    | s ->
       output_line stdout "unrecognized input";
       prompt ()
  in prompt ()

(* Call Coq on out_filename and prompt user to update in_filename with patch *)
let call_coq_prompt in_filename out_filename hint line =
  chain_processors
    (call_coq_define in_filename out_filename hint line)
    (prompt_overwrite in_filename out_filename)

(* Call Coq on out_filename and update in_filename with patch *)
let call_coq_overwrite in_filename out_filename hint line =
  chain_processors
    (call_coq_define in_filename out_filename hint line)
    (overwrite in_filename out_filename)
