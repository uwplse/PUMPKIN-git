(*
 * Utility methods
 *)

(* --- Lists --- *)

let flat_map f l = List.flatten (List.map f l)

let rec last_uniq l =
  match l with
  | h :: t ->
     let t' = last_uniq t in
     if List.mem h t' then
       t'
     else
       h :: t'
  | [] ->
     []

let non_empty (l : 'a list) = List.length l > 0

let sub (l2 : 'a list) (l1 : 'a list) : 'a list =
  List.filter (fun a -> not (List.mem a l1)) l2

