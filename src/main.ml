
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

(* Retrieve the content of a file at a particular git revision. *)
let retrieve filename revision identifier : in_channel =
  let script = replace "[$]IDENTIFIER" identifier retrieve_template in
  let command =
    Printf.sprintf
      "git show %s:%s | sed -n -E -e \"%s\"" (* Seems necessary to go through bash? *)
      revision (git_path filename) script
  in
  Unix.open_process_in command

(* Somewhat safely rename a Coq identifier in the given text. *)
let rename text identifier suffix : string list =
  let subst =
    replace
      ("\\([^A-Za-z0-9_']\\)" ^ identifier ^ "\\([^A-Za-z0-9_']\\|$\\)")
      ("\\1" ^ identifier ^ suffix ^ "\\2")
  in
  List.map subst text

(* Name the temporary output file *)
let output_filename filename : string =
  let prefix = Core.Std.Filename.chop_suffix filename ".v" in
  prefix ^ "_patch.v"

(* Insert the given text into the file's contents at the specified line. *)
let splice filename line text : unit =
  let pos = ref 0 in
  let input = open_in filename in
  let output = open_out (output_filename filename) in
  try
    while true do
      let buffer = input_line input in
      pos := !pos + 1;
      if line = !pos
      then
        (List.iter (output_line output) text;
         output_char output '\n');
      output_line output buffer
    done
  with End_of_file ->
    flush output;
    close_in input;
    close_out output

(* Get the line at which the given Coq identifier is defined/asserted. *)
let line_of filename identifier : int =
  let escaped = replace "'" "\'" identifier in
  let script = replace "[$]IDENTIFIER" escaped lineof_template in
  let command = Printf.sprintf "sed -n -E -e \"%s\" %s" script filename in
  Unix.open_process_in command |> slurp |> List.hd |> int_of_string

(* Perform a user command. *)
let run revision suffix dont_patch identifier filename () =
  let text = retrieve filename revision identifier |> slurp in
  if dont_patch
  then List.iter (output_line stdout) text
  else
    let line = line_of filename identifier in
    splice filename line (rename text identifier suffix)

let interface =
  let open Core.Command.Spec in
  empty
  +> flag "rev" (optional_with_default "HEAD~" string)
      ~doc:"object git revision of interest (default: HEAD~)"
  +> flag "suf" (optional_with_default "_old" string)
      ~doc:"string suffix to add to the older definition/proof (default: _old)"
  +> flag "show" no_arg
      ~doc:" print the old definition/proof instead of patching the file"
  +> anon ("identifier" %: string)
  +> anon ("filename" %: file)

let command =
  Core.Command.basic
    ~summary:"\
Get a previous version of a proof or definition from the local git history.\
"
    ~readme:(fun () -> "\
By default, an updated version of the specified file, patched with the renamed
proof or definition, is written to FILENAME_patch.v.\
")
    interface
    run

let () =
  Core.Command.run ~version:"0.1" command
