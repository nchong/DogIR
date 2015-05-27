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

type dog_t = {
  letdefs: letdef list;
  rules : G.t;
  asserts: dog_assert list;
}

let justedge (_,e,_) = e

let edge_between dog s s' =
  justedge (G.find_edge dog.rules s s')

let predecessors_of_state dog state =
  let rules = dog.rules in
  G.pred rules state

let successors_of_state dog state =
  let rules = dog.rules in
  G.succ rules state

let incoming_edges_of_state dog state =
  let rules = dog.rules in
  List.map justedge (G.pred_e rules state)

let outcoming_edges_of_state dog state =
  let rules = dog.rules in
  List.map justedge (G.succ_e rules state)

let trigger_states_of dog =
  nodups (List.fold_right (fun (s, _) states -> s::states) dog.asserts [])

let accepting_states_of dog =
  nodups (List.fold_right (fun (_, s') states -> s'::states) dog.asserts [])

let initial_states_of dog =
  let rules = dog.rules in
  gvertex_filter (fun v -> G.in_degree rules v = 0) rules

let vacuous_states_of dog =
  let rules, asserts = dog.rules, dog.asserts in
  let states_with_no_successors = gvertex_filter (fun v -> G.out_degree rules v = 0) rules in
  let states_in_asserts = trigger_states_of dog @ accepting_states_of dog in
  let vacuous = List.filter (fun v -> not (List.mem v states_in_asserts)) states_with_no_successors in
  vacuous

let events_of_path path =
  List.fold_right (fun expr acc -> (events_of_eventexpr expr) @ acc) path []

let graph_of_rule_list rules =
  List.fold_right (fun (s,s',e) g -> G.add_edge_e g (s,e,s')) rules G.empty

(* Copy graphs by mapping edges *)

module P(G:Sig.P) = struct
  module G = G
  let empty () = G.empty
  let add_edge_e = G.add_edge_e
end
module CopyWithEdgeMap = Gmap.Edge(G)(struct include G include P(G) end)

let expand_letdefs dog =
  let letdefs, rules, asserts = dog.letdefs, dog.rules, dog.asserts in
  let translate_edge edge =
    let (s,e,s') = edge in
    let e' = List.fold_right (fun ld -> substitute ld) letdefs e in
    (s,e',s')
  in
  let rules' = CopyWithEdgeMap.map translate_edge rules in
  {letdefs = []; rules = rules'; asserts}

(* Reachability *)

module Check = Path.Check(G)

let make_path_checker g =
  let path_checker = Check.create g in
  Check.check_path path_checker

(* returns a list of accepting paths 
   each path is a list [S0;S1;...;Sn] with S0 = init and Sn \in finals *)
let extract_paths rules init finals  =
  let adj = G.succ rules in
  let rec visit s path =
    if (List.mem s finals) then
      [ path ] @ List.fold_right (fun s' paths -> (visit s' (path @ [s'])) @ paths) (adj s) []
    else
      List.fold_right (fun s' paths -> (visit s' (path @ [s'])) @ paths) (adj s) []
  in
  visit init [init]

let edges_of_path rules path =
  let edge_between s s' =
    let _,e,_ = G.find_edge rules s s' in e
  in
  List.map (fun (s, s') -> edge_between s s') (allpairs path)

(* Dot interface *)

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

(* TODO: should deal with assert arrows too *)
let dottify dog fname =
  let rules = dog.rules in
  let file = open_out_bin fname in
  Dot.output_graph file rules
