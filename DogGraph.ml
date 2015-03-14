open Graph
open DogIR
open Lib

module Node = struct
  type t = state
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module Edge = struct
  type t = eventexpr
  let compare = Pervasives.compare (* is this ok? *)
  let equal = (=)
  let default = ExprIdentifier "default"
end

module G = Persistent.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)

let gvertex_filter pred g =
  G.fold_vertex (fun v acc -> if pred v then v::acc else acc) g []

let accepting_states_of (_, asserts)  =
  nodups (List.fold_right (fun (_, s') states -> s'::states) asserts [])

let initial_states_of (rules, _) =
  gvertex_filter (fun v -> G.in_degree rules v = 0) rules

type dog = G.t * dog_assert list

let graph_of_rule_list rules =
  List.fold_right (fun (s,s',e) g -> G.add_edge_e g (s,e,s')) rules G.empty

module Dot = Graph.Graphviz.Dot(struct
  include G
  let edge_attributes (a,e,b) =
    let label = string_of_eventexpr e in
    [`Label label;]
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes _ = [`Shape `Box]
  let vertex_name v = v
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end)
