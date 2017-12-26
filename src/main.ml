open Retrieve
open Strutils
open Ioutils
open Processors
open Outputters
open Changes (* TODO temporary *)

(*
 * Modes for running PUMPKIN-git:
 *
 * Show simply prints the old definition.
 * Define stores the old definition in a copy of the file.
 * Lazy is like Define, but adds (and doesn't execute) a call to PUMPKIN.
 * Call is like Lazy, but also executes the call to PUMPKIN.
 * Safe calls PUMPKIN for a patch, then saves it to a copy of the file.
 * Interactive prompts the user before adding the patch to the original file.
 * Force adds the patch directly to the file without prompting the user.
 *)
type mode = Show | Define | Lazy | Call | Safe | Interactive | Force

(*
 * Configurations for running PUMPKIN-git:
 *
 * The outputter outputs a definition and its dependencies in some way
 * to some channel (for example, to a Coq file).
 *
 * The processor the output and processes it in some way
 * (for example, running the Coq file to find a patch).
 *)
type config =
  {
    outputter : outputter;
    processor : processor;
  }

let lineof_template = "
/(Theorem|Lemma|Example|Definition|Let|Fixpoint|Inductive)[ ]+$IDENTIFIER[^A-Za-z0-9_']/{
  =
  q
}
"

(* Name the patch output file. *)
let output_filename filename : string =
  let prefix = Core.Std.Filename.chop_suffix filename ".v" in
  prefix ^ "_patch.v"

(* Get the line at which the definition of the given Coq identifier ends. *)
let line_of filename identifier text : int =
  let escaped = replace "'" "\'" identifier in
  let script = replace "[$]IDENTIFIER" escaped lineof_template in
  let command = Printf.sprintf "sed -n -E -e \"%s\" %s" script filename in
  let get_end i = i + List.length text in
  Unix.open_process_in command |> slurp |> List.hd |> int_of_string |> get_end

(* Determine what mode to run PUMPKIN-git in.*)
let get_mode mode =
  match mode with
  | "show" -> Show
  | "define" -> Define
  | "lazy" -> Lazy
  | "call" -> Call
  | "safe" -> Safe
  | "interactive" -> Interactive
  | "force" -> Force
  | _ -> failwith "unrecognized mode"

(* Configure how to output definitions. *)
let configure_outputter mode rev patch_id cut id filename line : outputter =
  let out_filename = output_filename filename in
  match mode with
  | Show ->
     show
  | Define ->
     define rev filename out_filename line
  | _ ->
     patch rev patch_id cut id filename out_filename line

(* Configure how to process the Coq file that calls PUMPKIN PATCH. *)
let configure_processor mode filename hint line : processor =
  let out_filename = output_filename filename in
  match mode with
  | Call ->
     call_coq_output out_filename
  | Safe ->
     call_coq_define filename out_filename hint line
  | Interactive ->
     call_coq_prompt filename out_filename hint line
  | Force ->
     call_coq_overwrite filename out_filename hint line
  | _ ->
     do_not_process

(* Configure a user command. *)
let configure_command mode rev hint patch_id cut id filename line =
  let outputter = configure_outputter mode rev patch_id cut id filename line in
  let processor = configure_processor mode filename hint line in
  { outputter; processor }

(* Perform a user command. *)
let run mode rev hint patch_id cut cl id filename () =
  let def = retrieve_def filename rev id in
  let line = line_of filename id def in
  let config = configure_command mode rev hint patch_id cut id filename line in
  let changed_deps = List.map (retrieve_def filename rev) cl in
  (* TODO temporary, before we fully integrate *)
  let graph = changed_dependencies filename id rev in
  output_using config.outputter def changed_deps;
  process_using config.processor

let interface =
  let open Core.Command.Spec in
  empty
  +> flag "mode" (optional_with_default "interactive" string)
      ~doc: "m run in one of these modes (default: interactive):\n
             \tshow: print the old definition/proof and then exit\n
             \tdefine: like show, but write to a temporary file\n
             \tlazy: like define, but add a call to PUMPKIN\n
             \tcall: like lazy, but execute the result\n
             \tsafe: write patched file to a temporary file\n
             \tinteractive: overwrite file with patched file\n
             \tforce: like interactive, but skip the user prompt"
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
