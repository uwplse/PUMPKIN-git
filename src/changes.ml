open Checksums

(*
 * Pull in all of the changed dependencies for a definition in
 * topologically sorted order.
 *
 * This is independent of the architecture that fetches the graph.
 * TODO move out node definition and graph fetching to a graph.ml file
 * that you will implement and sub with real architecture
 * TODO move out plural checksums to checksums ml file
 *)

type node = { id : string; adj : node list }

(* Get the dependency graph for a node *)
let dep_graph (id : string) =
  let adj = [] in { id ; adj } (* TODO not yet implemented *)

(* Initial guess for the number of definitions *)
let size = 500

(* Convenience methods (TODO move) *)
let flat_map f l = List.flatten (List.map f l)
let mem v n = Hashtbl.mem v n.id
let add v n = Hashtbl.add v n.id; v

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

let sub (l2 : 'a list) (l1 : 'a list) : 'a list =
  List.filter (fun a -> not (List.mem a l1)) l2

(* Get the checksums for all dependencies of a node *)
let checksums (n : node) : (string * string) list =
  let rec get_checksums v n =
    if mem v n then
      []
    else
      (n.id, checksum n.id) :: (flat_map (get_checksums (add v n)) n.adj)
  in get_checksums (Hashtbl.create size) n

(* Topologically sorted transitive changed dependencies *)
let taint (cs : (string * string) list) (n : node) : string list =
  let rec taint_nodes v n =
    if mem v n then
      []
    else
      let tainted = last_uniq (flat_map (taint_nodes (add v n)) n.adj) in
      if (List.length tainted > 0) || (List.mem_assoc n.id cs) then
        n.id :: tainted
      else
        []
  in taint_nodes (Hashtbl.create size) n

(* Check out an old git revision (TODO move to another file) *)
let checkout_rev (rev : string) : unit =
  () (* TODO implement *)
  (* TODO make sure this terminates before running rest of code *)

(* Go back to current revision, then reset to remove temp commit (TODO move) *)
let reset_revert (prev_rev : string) : unit =
  () (* TODO implement *)

(* Get the changed dependencies of a definition (inclusive) *)
let changed_dependencies (id : string) (rev : string) =
  let n' = dep_graph id in
  let cs_n' = checksums n' in
  checkout_rev rev;
  try
    let n = dep_graph id in
    let cs_n = checksums n in
    reset_revert "HEAD^";
    let cs = sub cs_n cs_n' in
    taint cs n
  with _ ->
    reset_revert "HEAD^";
    failwith "Could not identify dependencies"

