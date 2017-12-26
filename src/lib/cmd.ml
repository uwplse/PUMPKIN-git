(*
 * Utilities for command-line processes
 *)

(* Try to execute cmd with args, and fail with err if any status other than 0 *)
let try_execute (cmd : string) (args : string list) (err : string) =
  let cmd_with_args = String.concat " " (cmd :: args) in
  match Unix.system cmd_with_args with
  | WEXITED 0 ->
     ()
  | _ ->
     failwith err

