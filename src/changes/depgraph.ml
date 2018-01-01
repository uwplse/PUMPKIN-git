open Utilities
open Cmd
open Git

(*
 * Dependency graphs for Coq terms
 *)

type node = { id : string ; adj : node list ; checksum : string }
type graph = { root : node ; size : int }

(* --- Print a graph, for debugging --- *)

let rec node_as_string (n : node) : string =
  let adj = String.concat ",\n" (List.map (node_as_string) n.adj) in
  Printf.sprintf "{id: %s, checksum: %s, adj: [%s]}" n.id n.checksum adj

let graph_as_string (g : graph) : string =
  Printf.sprintf "size: %d, root: %s" g.size (node_as_string g.root)

let print_graph (g : graph) : unit =
  Printf.printf "%s\n" (graph_as_string g)

(* --- Generating and processing dot files --- *)

(*
 * I should probably move this outside of here since there are a lot
 * of utilities we need
 *)

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

(* Check if a statement is a node *)
let is_node (s : Odot.stmt) : bool =
  match s with
  | Stmt_node (_, _) ->
     true
  | _ ->
     false

(* Check if a statement is an edge *)
let is_edge (s : Odot.stmt) : bool =
  match s with
  | Stmt_edge _ ->
     true
  | _ ->
     false

(* Get the node id of a statement *)
let statement_node_id (s : Odot.stmt) : Odot.node_id =
  match s with
  | Stmt_node (nid, _) ->
     nid
  | _ ->
     failwith "not a node"

(* Get the edge statement from an edge *)
let edge_statement (s : Odot.stmt) : Odot.edge_stmt =
  match s with
  | Stmt_edge e ->
     e
  | _ ->
     failwith "not an edge"

(* Determine if an edge is from a particular node ID *)
let is_edge_from (nid : Odot.node_id) (e : Odot.edge_stmt) : bool =
  let (source, _, _) = e in
  match source with
  | Edge_node_id id ->
     id = nid
  | _ ->
     false (* TODO subgraph handling, which we need many places here *)

(* Get the edges from a node ID *)
let edges_from sl (nid : Odot.node_id) : Odot.edge_stmt list =
  let edges = List.map edge_statement (List.filter is_edge sl) in
  List.filter (is_edge_from nid) edges

(* Check whether an edge point is a node ID *)
let is_node_id (p : Odot.edge_stmt_point) : bool =
  match p with
  | Edge_node_id _ ->
     true
  | _ ->
     false

(* Get the node ID of an edge point *)
let edge_point_node_id (p : Odot.edge_stmt_point) : Odot.node_id =
  match p with
  | Edge_node_id id ->
     id
  | _ ->
     failwith "can't get node ID from a subgraph"

(* Get the node with the supplied ID from a statement list *)
let node_with_id sl (nid : Odot.node_id) : Odot.stmt =
  try
    List.find (fun s -> statement_node_id s = nid) (List.filter is_node sl)
  with _ ->
    failwith "node ID not found"

(* Get destination nodes from an edge *)
let destinations sl (e : Odot.edge_stmt) : Odot.stmt list  =
  let (_, dest_pts, _) = e in
  let dest_node_ids = List.map edge_point_node_id dest_pts in
  List.map (node_with_id sl) dest_node_ids

(* Get the statements that are adjacent to a statement *)
let adjacent_statements sl (s : Odot.stmt) : Odot.stmt list =
  if is_node s then
    List.flatten
      (List.map
         (destinations sl)
         (edges_from sl (statement_node_id s)))
  else
    []

(* Process a statement *)
let rec process_statement sl (s : Odot.stmt) : node =
  let id = attr_value "label" s in
  let adj = List.map (process_statement sl) (adjacent_statements sl s) in
  let checksum = id in (* TODO *)
  { id ; adj ; checksum }

(* Process a list of statements *)
let process_statements (root_s : Odot.stmt) (sl : Odot.stmt list) : graph =
  let root = process_statement sl root_s in
  let size = List.length (List.filter is_node sl) in
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
  in
  let cs = get_checksums (create g) (root g) in
  List.iter (fun (id, _) -> Printf.printf "%s\n" id) cs;
  Printf.printf "%s\n\n" "----";
  cs
