(*
 * Utility methods
 *)

(* --- Lists --- *)

val flat_map : ('a -> 'b list) -> 'a list -> 'b list
val non_empty : 'a list -> bool

(*
 * Filter out duplicate elements
 * Keep the last element when there are duplicates
 *)
val last_uniq : 'a list -> 'a list

(*
 * Return all elements of the first list that are not in the second list
 *)
val sub : 'a list -> 'a list -> 'a list


