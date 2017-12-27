open Utilities
open Cmd
open Git

(*
 * Dependency graphs for Coq terms
 *)

type node = { id : string ; adj : node list ; checksum : string }
type graph = { root : node ; size : int }

(* --- Generating and processing dot files --- *)

(* Generate the dot file *)
let generate_dot (filename : string) (id : string) : unit =
  let dot_script = Printf.sprintf "%s%s" (git_root ()) "/src/dpdgraph.sh" in
  checkout_file dot_script "-";
  try_execute
    dot_script
    [filename; id]
    "Failed to generate .dot file for dependency graph"

(* Check if the statement has an attribute *)
let has_attr (aid : string) (s : Odot.stmt) : bool =
  match s with
  | Stmt_node (_, attrs) ->
     List.mem_assoc (Odot.Simple_id aid) attrs
  | _ ->
     false

(* Get the value of the attribute with a given ID for a statement *)
let attr_value (aid : string) (s : Odot.stmt) : string =
  match s with
  | Stmt_node (_, attrs) ->
     (match List.assoc (Odot.Simple_id aid) attrs with
      | Some (Odot.Simple_id id) -> id
      | Some (Odot.Html_id id) -> id
      | Some (Odot.Double_quoted_id id) -> id
      | None -> "")
  | _ ->
     failwith "attribute not found"

(* Process a list of statements *)
let process_statements (root_s : Odot.stmt) (sl : Odot.stmt list) : graph =
  let id = attr_value "label" root_s in
  Printf.printf "found id: %s\n\n" id;
  let adj = [] in (* TODO *)
  let checksum = id in (* TODO *)
  let root = { id ; adj ; checksum } in
  let size = 1 in (* TODO *)
  { root ; size }

(* Identify the root statement *)
let find_root_statement (root_id : string) (sl : Odot.stmt list) : Odot.stmt =
  List.find
    (fun s ->
      if has_attr "label" s then
        attr_value "label" s = root_id
      else
        false)
    sl

(* Process the dot file *)
let process_dot (dot_filename : string) (root_id : string) : graph =
  let parsed = Odot.parse_file dot_filename in
  let root_s = find_root_statement root_id parsed.stmt_list in
  process_statements root_s parsed.stmt_list

(* --- Graphs --- *)

(* Get the dependency graph for a definition and return the root node *)
let dep_graph (filename : string) (id : string) : graph =
  generate_dot filename id;
  process_dot "graph.dot" id

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
