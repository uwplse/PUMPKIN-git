open Ioutils

(*
 * Git utilities
 *)

let stash () =
  match Unix.system "git stash" with
  | WEXITED 0 ->
     ()
  | _ ->
     failwith "Could not stash; please commit current work and try again"

let stash_pop () =
  match Unix.system "git stash pop" with
  | WEXITED 0 ->
     ()
  | _ ->
     failwith "Could not pop stash; Git state may be inconsistent"

let checkout (rev : string) : unit =
  match Unix.system (Printf.sprintf "git checkout %s" rev) with
  | WEXITED 0 ->
     ()
  | _ ->
     failwith "Could not checkout revision; Git state may be inconsistent"

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


