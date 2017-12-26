open Depgraph
open Utilities
open Git

(*
 * Pull in all of the changed dependencies for a definition in
 * topologically sorted order.
 *
 * This is independent of the architecture that fetches the graph.
 *
 * Current algorithm:
 * 1. Get the dependency graphs n (old) and n' (new)
 * 2. Map each ID to a checksum in both n and n'
 * 3. Filter out everything in checksums(n) that either has a different ID
 *    or a different checksum
 * 4. Transitively taint nodes that have dependencies that have changed
 *    (invalidate the upward transitive closure)
 * 5. Return tainted IDs in topologically sorted order
 *)

(* Topologically sorted transitive changed dependencies *)
let taint (cs : (string * string) list) (g : graph) : string list =
  let rec taint_nodes v n =
    if IDHashtbl.mem v n then
      []
    else
      let tainted = last_uniq (flat_map (taint_nodes (add v n)) (adjacent n)) in
      if non_empty tainted || List.mem_assoc (node_id n) cs then
        node_id n :: tainted
      else
        []
  in taint_nodes (create g) (root g)

(* Get the changed dependencies of a definition (inclusive) *)
let changed_dependencies (id : string) (rev : string) =
  let g' = dep_graph id in
  let cs_g' = checksums g' in
  stash ();
  try
    checkout rev;
    let g = dep_graph id in
    let cs_g = checksums g in
    checkout "HEAD";
    stash_pop ();
    let cs = sub cs_g cs_g' in
    taint cs g
  with Failure f -> (* TODO implement try/finally, catch all errors *)
    try
      checkout "HEAD";
      stash_pop ();
      failwith (String.concat ": " ["Could not identify dependencies"; f])
    with Failure f_git ->
      stash_pop ();
      failwith f_git
