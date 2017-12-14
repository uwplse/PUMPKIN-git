open Utilities

(*
 * Dependency graphs for Coq terms
 *)

type node = { id : string ; adj : node list ; checksum : string }
type graph = { root : node ; size : int }

(* --- Graphs --- *)

(* Get the dependency graph for a definition and return the root node *)
let dep_graph (id : string) : graph =
  let adj = [] in
  let checksum = id in
  let root = { id ; adj ; checksum } in
  let size = 1 in
  { root ; size } (* TODO not yet implemented, call icoq *)

let root g = g.root
let size g = g.size

(* --- Nodes --- *)

(* Get the nodes adjacent to a node *)
let adjacent (n : node) : node list = n.adj

let node_id n = n.id
let checksum n = n.checksum

(* --- Hashing nodes --- *)

module IDHash =
  struct
    type t = node
    let equal n1 n2 = (node_id n1 = node_id n2)
    let hash n = Hashtbl.hash (node_id n)
  end

module IDHashtbl = Hashtbl.Make(IDHash)

let add v n = IDHashtbl.add v n; v

(* --- Operations on Dependencies --- *)

(* Get the checksums for all dependencies of the root node in a graph *)
let checksums (g : graph) : (string * string) list =
  let rec get_checksums v n =
    if IDHashtbl.mem v n then
      []
    else
      let id_checksum = (node_id n, checksum n) in
      id_checksum :: (flat_map (get_checksums (add v n)) (adjacent n))
  in get_checksums (IDHashtbl.create (size g)) (root g)
