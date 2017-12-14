(* --- String utilities --- *)

(* Find and replace with a regex. *)
let replace pat sub str =
  Str.global_replace (Str.regexp pat) sub str
