open Ioutils
open Strutils

(* --- Retrieve Coq definitions and dependencies from Git --- *)

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

(* Retrieve definition of id at revision rev in filename as a list of strings *)
let retrieve_def filename rev id : string list =
  retrieve filename rev id |> slurp
