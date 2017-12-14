(*
 * Dependency graphs for Coq terms
 *)

type graph
type node

(* --- Graphs --- *)

(*
 * Get the dependency graph from a definition identifier
 *)
val dep_graph : string -> graph

(*
 * Get the root node of a dependency graph
 *)
val root : graph -> node

(*
 * Get the size of a dependency graph
 *)
val size : graph -> int

(* --- Nodes --- *)

(*
 * Get the nodes adjacent to a node
 *)
val adjacent : node -> node list

(*
 * Get the fully-qualified ID of a node
 *)
val node_id : node -> string

(*
 * Get the checksum of a node
 *)
val checksum : node -> string

(* --- Hashing nodes --- *)

(*
 * Hash nodes by identifiers
 *)
module IDHashtbl : Hashtbl.S with type key = node

(*
 * Add with return
 *)
val add : 'a IDHashtbl.t -> node -> 'a IDHashtbl.t

(* --- Operations on Dependencies --- *)

(*
 * Get a map of IDs to checksums for all dependencies of the graph's root node
 * Include the root node itself
 *)
val checksums : graph -> (string * string) list
