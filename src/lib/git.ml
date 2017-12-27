open Ioutils
open Cmd
open Utilities

(*
 * Git utilities
 *)

(* --- Basic git functionality --- *)

let stash () =
  try_execute
    "git stash"
    []
    "Could not stash; please commit current work and try again"

let stash_pop () =
  try_execute
    "git stash pop"
    []
    "Could not pop stash; Git state may be inconsistent"

let checkout (rev : string) : unit =
  try_execute
    "git checkout"
    [rev]
    "Could not checkout revision; Git state may be inconsistent"

let checkout_file (filename : string) (rev : string) : unit =
  try_execute
    "git checkout"
    [rev; "--"; filename]
    "Could not checkout file from revision; Git state may be inconsistent"

let diff () : string list =
  Unix.open_process_in "git diff" |> slurp

(* --- Complex sequences of commands --- *)

(* Return a command that runs if and only if a condition is met *)
let run_iff (condition : bool) (command : unit -> unit) : unit -> unit =
  if condition then
    command
  else
    (fun _ -> ())

(* Check if there are any local uncommitted changes *)
let has_uncommitted () : bool =
  diff () |> non_empty

(* Get the root directory of the local git repository. *)
let git_root () =
  Unix.open_process_in "git rev-parse --show-toplevel" |> slurp |> List.hd

(* Get the path to a file relative to the git repository's root directory. *)
let git_path filename =
  let path = Core.Std.Filename.realpath filename in
  let root = git_root () in
  let pos = String.length root + 1 in
  let len = String.length path - String.length root - 1 in
  String.sub path pos len


