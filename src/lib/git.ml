(*
 * Git utilities
 *)

let stash () =
  match Unix.system "git stash" with
  | Ok _ ->
     ()
  | _ ->
     failwith "Could not stash; please commit current work and try again"

let stash_pop () =
  () (* TODO implement *)

let checkout (rev : string) : unit =
  () (* TODO implement *)

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


