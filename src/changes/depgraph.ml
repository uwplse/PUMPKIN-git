open Utilities
open Cmd
open Git

(*
 * Dependency graphs for Coq terms
 *
 * TODO need to make this more efficient
 * TODO need to fetch fully-qualified IDs by supporting subgraphs
 * TODO need to get checksums
 * TODO need to exclude constructors and cases
 *)

(* The size of a graph is a rough approximation of the number of nodes *)
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

(* Get an identifier as a string *)
let id_to_string (id : Odot.id) : string =
  match id with
  | Odot.Simple_id id -> id
  | Odot.Html_id id -> id
  | Odot.Double_quoted_id id -> id

(* Get the value of the attribute with a given ID *)
let attr_value (aid : string) (attrs : Odot.attr list) : string =
  try
    (match List.assoc (Odot.Simple_id aid) attrs with
     | Some id ->
        id_to_string id
     | None ->
        "")
  with _ ->
    ""

(* Get the value of the attribute with a given ID for a statement *)
let attr_value_stmt (aid : string) (s : Odot.stmt) : string =
  match s with
  | Stmt_node (_, attrs) ->
     attr_value aid attrs
  | _ ->
     failwith "attribute not found"

(* Check if a statement is a node *)
let is_node (s : Odot.stmt) : bool =
  match s with
  | Stmt_node (_, _) ->
     true
  | _ ->
     false

(* Check if a statement is a subgraph *)
let is_subgraph (s : Odot.stmt) : bool =
  match s with
  | Stmt_subgraph g ->
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

(* Get an attribute from an equals statement  *)
let attr_of_equals (s : Odot.stmt) : Odot.attr =
  match s with
  | Stmt_equals (idl, idr) ->
     (idl, Some idr)
  | _ ->
     failwith "not an equals statement"

(* Check if a statement is an attribute *)
let is_attr (s : Odot.stmt) : bool =
  match s with
  | Stmt_attr _ ->
     true
  | _ ->
     false

(* Check if a statement is an equality *)
let is_equals (s : Odot.stmt) : bool =
  match s with
  | Stmt_equals _ ->
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
     false

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

(* Get the fully-qualified ID of a statement *)
let get_fq_id fq_ids (s : Odot.stmt) : string =
  let id = attr_value_stmt "label" s in
  try
    List.assoc id fq_ids
  with _ ->
    id

(* Qualify a single ID with a prefix *)
let qualify (prefix : string) (id : string) =
  if String.length prefix = 0 then
    id
  else
    String.concat "." [prefix; id]

(* Trim a prefix off of an ID *)
let unqualify (prefix : string) (id : string) =
  String.sub id (String.length prefix) (String.length id)

(* Get the fully qualified IDs *)
let rec get_fq_ids prefix subgraphs : (string * string) list =
  flat_map
    (fun subgraph ->
      match subgraph with
      | Odot.Stmt_subgraph s ->
         let sub_stmts = s.sub_stmt_list in
         let equals = List.filter is_equals sub_stmts in
         let attrs = List.map attr_of_equals equals in
         let label = attr_value "label" attrs in
         let qualified = qualify prefix label in
         let fqs =
           List.map
             (fun n ->
               let (id, _) = statement_node_id n in
               let label_n = unqualify qualified (id_to_string id) in
               (label_n, qualify qualified label_n))
             (List.filter is_node sub_stmts)
         in
         List.append
           fqs
           (get_fq_ids qualified (List.filter is_subgraph sub_stmts))
      | _ ->
         failwith "not a subgraph")
    subgraphs

(* Process a statement *)
let rec process_statement sl fq_ids (s : Odot.stmt) : node =
  let id = get_fq_id fq_ids s in
  let adj = List.map (process_statement sl fq_ids) (adjacent_statements sl s) in
  let checksum = id in (* TODO *)
  { id ; adj ; checksum }

(* Process a list of statements *)
let process_statements (root_s : Odot.stmt) (sl : Odot.stmt list) : graph =
  let subgraphs = List.filter is_subgraph sl in
  let fq_ids = get_fq_ids "" subgraphs in
  List.iter (fun (id, fq) -> Printf.printf "%s: %s\n" id fq) fq_ids;
  let root = process_statement sl fq_ids root_s in
  let size = List.length (List.filter is_node sl) in
  { root ; size }

(* Identify the root statement *)
let find_root_statement (root_id : string) (sl : Odot.stmt list) : Odot.stmt =
  List.find
    (fun s ->
      if has_attr "label" s then
        attr_value_stmt "label" s = root_id
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

let add h n v = IDHashtbl.add h n v; h
let create g = IDHashtbl.create (size g)

(* --- Operations on Dependencies --- *)

(* Get the checksums for all dependencies of the root node in a graph *)
let checksums (g : graph) : (string * string) list =
  let rec get_checksums h n =
    if IDHashtbl.mem h n then
      []
    else
      let id_check = (node_id n, checksum n) in
      id_check :: (flat_map (get_checksums (add h n ())) (adjacent n))
  in
  let cs = get_checksums (create g) (root g) in
  List.iter (fun (id, _) -> Printf.printf "%s\n" id) cs;
  Printf.printf "%s\n\n" "----";
  cs
