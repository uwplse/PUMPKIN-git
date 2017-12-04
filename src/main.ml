(* Modes for running PUMPKIN-git *)
type mode = Default | Show | Safe | Force

(* This is the sed template, embedded as a string for convenience. *)
let retrieve_template = "
/(Theorem|Lemma|Example)[ ]+$IDENTIFIER[^A-Za-z0-9_']/{
  :prf
  p
  /(Qed|Admitted|Defined)[.]/!{
    n
    b prf
  }
  q
}

/(Definition|Let|Fixpoint|CoFixpoint)[ ]+$IDENTIFIER[^A-Za-z0-9_']/{
  :def
  p
  /[^.][.]([ ]*[(][*].*[*][)])*[ ]*$/!{
    n
    b def
  }
  q
}

/(Inductive|CoInductive)[ ]+$IDENTIFIER[^A-Za-z0-9_']/{
  :ind
  p
  /[^.][.]([ ]*[(][*].*[*][)])*[ ]*$/!{
    n
    b ind
  }
  q
}
"

let lineof_template = "
/(Theorem|Lemma|Example|Definition|Let|Fixpoint|Inductive)[ ]+$IDENTIFIER[^A-Za-z0-9_']/{
  =
  q
}
"

let slurp ch =
  let buf = ref [] in
  try
    while true do
      buf := input_line ch :: !buf
    done;
    !buf
  with End_of_file ->
    close_in ch;
    List.rev !buf

(* Get the root directory of the local git repository. *)
let git_root () =
  Unix.open_process_in "git rev-parse --show-toplevel" |> slurp |> List.hd

(* Get the path to a file relative to the git repository's root directory. *)
let git_path filename =
  let path = Core.Filename.realpath filename in
  let root = git_root () in
  let pos = String.length root + 1 in
  let len = String.length path - String.length root - 1 in
  String.sub path pos len

(* Why isn't this part of the standard library? *)
let output_line ch s =
  output_string ch s;
  output_char ch '\n'

(* Find and replace with silly regex type. *)
let replace pat sub str =
  Str.global_replace (Str.regexp pat) sub str

(* Retrieve just the identifier at a particular git revision. *)
let retrieve filename rev id : in_channel =
  let script = replace "[$]IDENTIFIER" id retrieve_template in
  let command =
    Printf.sprintf
      "git show %s:%s | sed -n -E -e \"%s\"" (* Seems necessary to go through bash? *)
      rev
      (git_path filename)
      script
  in Unix.open_process_in command

(* Retrieve the identifier as a list of strings *)
let retrieve_text filename rev id : string list =
  retrieve filename rev id |> slurp

(* Wrap the text in a module *)
let wrap_in_module text name : string list =
  let open_module = Printf.sprintf "Module %s.\n" name in
  let close_module = Printf.sprintf "\nEnd %s." name in
  open_module :: (List.append text [close_module])

(* Name the patch output file. *)
let output_filename filename : string =
  let prefix = Core.Filename.chop_suffix filename ".v" in
  prefix ^ "_patch.v"

(* Insert the given text into the file's contents at the specified line. *)
let splice input_filename output_filename line text : unit =
  let pos = ref 0 in
  let input = open_in input_filename in
  let output = open_out output_filename in
  try
    while true do
      let buffer = input_line input in
      pos := !pos + 1;
      if line = !pos then
        (List.iter (output_line output) text;
         output_char output '\n');
      output_line output buffer
    done
  with End_of_file ->
    if !pos < line then
      (List.iter (output_line output) text;
       output_char output '\n');
    flush output;
    close_in input;
    close_out output

(* Append the text that calls PUMPKIN to the end of the file. *)
let call_pumpkin patch_id id module_name cut =
  let import = "Require Import Patcher.Patch.\n" in
  let set_printing = "Set PUMPKIN Printing.\n\n" in
  let old_id = Printf.sprintf "%s.%s" module_name id in
  let patch =
    if Core.Option.is_some cut then
      let app = Core.Option.value_exn cut in
      Printf.sprintf "Patch Proof %s %s cut by %s as %s." old_id id app patch_id
    else
      Printf.sprintf "Patch Proof %s %s as %s." old_id id patch_id
  in [import; set_printing; patch; "\n\n"]

(* Get the line at which the definition of the given Coq identifier ends. *)
let line_of filename identifier text : int =
  let escaped = replace "'" "\'" identifier in
  let script = replace "[$]IDENTIFIER" escaped lineof_template in
  let command = Printf.sprintf "sed -n -E -e \"%s\" %s" script filename in
  let get_end i = i + List.length text in
  Unix.open_process_in command |> slurp |> List.hd |> int_of_string |> get_end

(* Check whether a given line marks the end of a patch *)
let is_end_line s =
  s = "END PATCH"

(* Get a patch definition from pretty-printed output *)
let pp_to_def hint pp : string =
  let begin_patch_pat = Str.regexp "BEGIN PATCH .*" in
  let pp =
    List.rev
      (Core.List.take_while
         (List.tl (List.rev pp))
         (fun s -> not (Str.string_match begin_patch_pat s 0)))
  in
  let comment = "\n(* Auto-generated by PUMPKIN-git *)" in
  let def = String.concat "\n" (comment :: pp) in
  if hint then
    let id = List.hd (List.tl (Str.split (Str.regexp "[ ]+") (List.hd pp))) in
    Printf.sprintf "%s\n\nHint Resolve %s." def id
  else
    def

(* Overwrite input_filename with output_filename *)
let overwrite input_filename output_filename =
  let rewrite = Printf.sprintf "mv %s %s" output_filename input_filename in
  match Unix.system rewrite with
   | Unix.WEXITED 0 ->
      ()
   | _ ->
      failwith "Cannot overwrite file. Check permissions."

(* Prompt user to overwrite file *)
let prompt_overwrite input_filename output_filename =
  let diff = Printf.sprintf "diff %s %s" input_filename output_filename in
  output_line stdout "pumpkin-git wants to make the following changes:\n";
  Unix.open_process_in diff |> slurp |> List.iter (output_line stdout);
  let rec prompt () =
    output_line stdout (Printf.sprintf "\noverwrite %s? [y/n]" input_filename);
    match read_line () with
    | "y" ->
       overwrite input_filename output_filename
    | "n" ->
       ()
    | s ->
       output_line stdout "unrecognized input";
       prompt ()
  in prompt ()

(* Define the patch term without referring to the changed term. *)
let define_patch mode input_filename output_filename hint line input : unit =
  let marks_end s1 _ = is_end_line s1 in
  let defs = Core.List.group input ~break:marks_end in
  let patches = List.map (pp_to_def hint) defs in
  splice input_filename output_filename line patches;
  if not (mode = Safe) then
    if not (mode = Force) then
      prompt_overwrite input_filename output_filename
    else
      overwrite input_filename output_filename

(* Determine what mode to run PUMPKIN-git in.*)
let get_mode mode =
  match mode with
  | Some "show" -> Show
  | Some "safe" -> Safe
  | Some "force" -> Force
  | None -> Default
  | _ -> failwith "unrecognized mode"

(* Perform a user command. *)
let run mode rev hint patch_id cut cl id filename () =
  let text = retrieve_text filename rev id in
  let changed_defs = List.flatten (List.map (retrieve_text filename rev) cl) in
  if mode = Show then
    List.iter (output_line stdout) (List.append changed_defs text)
  else
    let line = line_of filename id text in
    let module_name = "rev" ^ rev in
    let old_text = wrap_in_module (List.append changed_defs text) module_name in
    let patch_text = call_pumpkin patch_id id module_name cut in
    let out_filename = output_filename filename in
    splice filename out_filename line (List.append old_text patch_text);
    let run_coq = Printf.sprintf "coqc %s" out_filename in
    let patch = define_patch mode filename out_filename hint line in
    Unix.open_process_in run_coq |> slurp |> patch

let interface =
  let open Core.Command.Spec in
  empty
  +> flag "mode" (optional string)
      ~doc: "m run in one of these modes:\n
             \tshow: print the old definition/proof instead of patching\n
             \tsafe: write patched file to a different file\n
             \tforce: do not prompt to overwrite file"
  +> flag "rev" (optional_with_default "HEAD" string)
      ~doc:"object git revision of interest (default: HEAD)"
  +> flag "hint" no_arg
      ~doc:" add the patch to the hint database"
  +> flag "patch" (optional_with_default "patch" string)
      ~doc:" name of the patch (default: patch)"
  +> flag "cut" (optional string)
      ~doc:"app lemma and arguments to cut by"
  +> flag "changed" (listed string)
      ~doc:"def additional definitions that have changed"
  +> anon ("identifier" %: string)
  +> anon ("filename" %: file)

let command =
  Core.Command.basic
    ~summary:"\
Find a patch between the current version and a previous version of a
proof or definition from the local git history.\
"
    ~readme:(fun () -> "\
By default, an updated version of the specified file
with a patch between versions is written to the file.\
")
    interface
    (fun mode -> run (get_mode mode))

let () =
  Core.Command.run ~version:"0.1" command
