open Ioutils

(* --- Outputting Definitions and Dependencies --- *)

(*
 * An outputter takes the text of a definition (as a list of strings)
 * and the text of its dependencies (a list of lists of strings) and
 * outputs it in some way to some channel (for example, to standard out
 * or to a file).
 *)
type outputter = string list -> string list list -> unit

(* Convenience method *)
let def_with_deps def deps =
  List.append (List.flatten deps) def

(* Wrap the text in a module *)
let wrap_in_module text name : string list =
  let open_module = Printf.sprintf "Module %s.\n" name in
  let close_module = Printf.sprintf "\nEnd %s." name in
  open_module :: (List.append text [close_module])

(* Wrap the definition and dependencies in a module for the revision *)
let wrap_defs_in_module rev def deps =
  let module_name = "rev" ^ rev in
  wrap_in_module (def_with_deps def deps) module_name

(* Append the text that calls PUMPKIN to the end of the file. *)
let call_pumpkin patch_id id rev cut =
  let import = "Require Import Patcher.Patch.\n" in
  let set_printing = "Set PUMPKIN Printing.\n\n" in
  let old_id = Printf.sprintf "%s.%s" ("rev" ^ rev) id in
  let patch =
    if Core.Option.is_some cut then
      let app = Core.Option.value_exn cut in
      Printf.sprintf "Patch Proof %s %s cut by %s as %s." old_id id app patch_id
    else
      Printf.sprintf "Patch Proof %s %s as %s." old_id id patch_id
  in [import; set_printing; patch; "\n\n"]

(* Call the outputter *)
let output_using outputter def deps =
  outputter def deps

(* --- Built-in Outputters ---*)

(* Print the definition and its dependencies to stdout *)
let show def deps =
  output_lines stdout (List.append (List.flatten deps) def)

(* Add the definition and its dependencies to a file wrapped in a module *)
let define rev in_filename out_filename line def deps =
  splice in_filename out_filename line (wrap_defs_in_module rev def deps)

(* Add the definition and its dependencies, then add calls to PUMPKIN *)
let patch rev patch_id cut id in_filename out_filename line def deps =
  let text = wrap_defs_in_module rev def deps in
  let patch_text = call_pumpkin patch_id id rev cut in
  splice in_filename out_filename line (List.append text patch_text)
