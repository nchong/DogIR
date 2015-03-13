open Graph
open DogIR

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
