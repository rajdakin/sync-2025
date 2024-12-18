type vertex = int
type graph = int list array
type color = White | Grey | Black

(** Returns the same list without the duplicate elements *)
let rec remove_dup (l : 'a list) : 'a list =
  match l with
  | [] -> []
  | x :: l -> if Stdlib.List.mem x l then remove_dup l else x :: remove_dup l

(** Reorder the first list according to the order of the its first elements as
    they appear in the second list *)
let rec reorder_list (l : ('a * 'b) list) (order : 'a list) : ('a * 'b) list =
  match order with
  | [] -> []
  | v :: order -> (v, Stdlib.List.assoc v l) :: reorder_list l order

(** Check whether a graph contains a cycle: returns [None] if not and [Some] of
    two elements in a cycle otherwise *)
let has_cycle (g : graph) : (vertex * vertex) option =
  let n = Array.length g in
  let visited = Array.make n White in
  let cycle_detected = ref None in
  let rec dfs (v : vertex) : unit =
    visited.(v) <- Grey;
    Stdlib.List.iter
      (fun u ->
        if visited.(u) = Grey then cycle_detected := Some (u, v)
        else if visited.(u) = White then dfs u)
      g.(v);
    visited.(v) <- Black
  in
  for i = 0 to n - 1 do
    if visited.(i) = White then dfs i
  done;
  !cycle_detected

(** Return a topological sort of the given graph that is assumed to be acyclic
*)
let topological_sort (g : graph) : vertex list =
  let n = Array.length g in
  let visited = Array.make n false in
  let order = ref [] in
  let rec dfs (v : vertex) : unit =
    if not visited.(v) then (
      visited.(v) <- true;
      Stdlib.List.iter dfs g.(v);
      order := v :: !order)
  in
  for i = 0 to n - 1 do
    dfs i
  done;
  !order

(** Converts a node's body into a graph *)
let node_to_graph (node : Lustre.node) : graph * (int, vertex) Hashtbl.t =
  let n = Stdlib.List.length node.n_in + Stdlib.List.length node.n_locals + 1 in
  let g = Array.make n [] in
  let var_table = Hashtbl.create n in
  let index_table = Hashtbl.create n in
  let var_idx (v : vertex) : int =
    if Hashtbl.mem var_table v then Hashtbl.find var_table v
    else
      let value = v in
      Hashtbl.add var_table v value;
      Hashtbl.add index_table value v;
      value
  in
  Stdlib.List.iter
    (fun (v, exp) ->
      let vars = remove_dup @@ Lustre.var_of_exp exp in
      Stdlib.List.iter (fun u -> ignore @@ var_idx u) vars;
      g.(var_idx v) <- vars)
    node.n_body;
  (g, index_table)

(** Orders the equations in a node *)
let node_ordering (node : Lustre.node) : LustreOrdered.node_ordered Result.t =
  let graph, index_table = node_to_graph node in
  match has_cycle graph with
  | None ->
      let new_order =
        reorder_list node.n_body
          (List.map
             (fun idx -> Hashtbl.find index_table idx)
             (topological_sort graph))
      in
      let new_node = { node with n_body = new_order } in
      Result.Ok new_node
  | Some (u, v) ->
      Result.Err
        (Printf.sprintf "The variables %d and %d are mutually recursive" u v)
