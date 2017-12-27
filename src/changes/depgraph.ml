open Utilities
open Cmd
open Git

(*
 * Dependency graphs for Coq terms
 *)

type node = { id : string ; adj : node list ; checksum : string }
type graph = { root : node ; size : int }

(* --- Graphs --- *)

(* Generate the dot file *)
let generate_dot (filename : string) (id : string) =
  let root_dir = git_root () in
  checkout_file (Printf.sprintf "%s%s" root_dir "/src/dpdgraph.sh") "-";
  try_execute
    "dpdgraph.sh"
    [filename; id]
    "Failed to generate .dot file for dependency graph"

(* Get the dependency graph for a definition and return the root node *)
let dep_graph (filename : string) (id : string) : graph =
  generate_dot filename id;
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
let create g = IDHashtbl.create (size g)

(* --- Operations on Dependencies --- *)

(* Get the checksums for all dependencies of the root node in a graph *)
let checksums (g : graph) : (string * string) list =
  let rec get_checksums v n =
    if IDHashtbl.mem v n then
      []
    else
      let id_checksum = (node_id n, checksum n) in
      id_checksum :: (flat_map (get_checksums (add v n)) (adjacent n))
  in get_checksums (create g) (root g)
