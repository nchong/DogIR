open DogIR
open DogGraph
open Lib

(* Fresh variable generator for ranging over events *)
let efresh_name = gen_counter "e"
(* Fresh variable generator for ranging over earlier events *)
let ffresh_name = gen_counter "f"
(* Fresh variable generator for ranging over vacuous escape events *)
let xfresh_name = gen_counter "x"

type dog_constraint =
| ConstraintFalse
| ConstraintTrue
| ConstraintMatch of identifier * event list
| ConstraintComplete of identifier * identifier list
| ConstraintStarOrdered of identifier * identifier        (* (e1,e2) \in so *)
| ConstraintClockOrdered of identifier * identifier       (* (e1,e2) \in ct_leq *)
| ConstraintClockOrderedStrict of identifier * identifier (* (e1,e2) \in ct_lt *)
| ConstraintNot of dog_constraint
| ConstraintAnd of dog_constraint list
| ConstraintOr of dog_constraint list
| ConstraintImplies of dog_constraint * dog_constraint
| ConstraintExists of (identifier list) * dog_constraint (* \exists e0 e1 ... \in Ev :: ... *)

let flatten termof xs =
  let rec aux acc = function
    | [] -> acc
    | c::cs -> aux (acc @ termof c) cs
  in
  aux [] xs

let conjunct constraints =
  match constraints with
  | [] -> ConstraintTrue
  | _ -> ConstraintAnd (flatten (function | ConstraintAnd cs -> cs | _ as c -> [c]) constraints)

let disjunct constraints =
  match constraints with
  | [] -> ConstraintTrue
  | _ -> ConstraintOr (flatten (function | ConstraintOr cs -> cs | _ as c -> [c]) constraints)

(* v,w range over identifiers *)
let rec string_of_constraint = function
| ConstraintFalse -> Format.sprintf "false"
| ConstraintTrue -> Format.sprintf "true"
| ConstraintMatch (v, events) -> Format.sprintf "@[(%s matches {%s})@]" v (String.concat ", " (List.map string_of_event events))
| ConstraintComplete (v, starts) -> Format.sprintf "@[isComplete(%s, {%s})@]" v (String.concat ", " starts)
| ConstraintStarOrdered (v, w) -> Format.sprintf "@[SO<=(%s,@ %s)@]" v w
| ConstraintClockOrdered (v, w) -> Format.sprintf "@[CT<=(%s,@ %s)@]" v w
| ConstraintClockOrderedStrict (v, w) -> Format.sprintf "@[CT<(%s,@ %s)@]" v w
| ConstraintNot subterm -> Format.sprintf "not(@[%s@])" (string_of_constraint subterm)
| ConstraintAnd conjuncts -> Format.sprintf "@[%s@]" (String.concat " /\\ " (List.map string_of_constraint conjuncts))
| ConstraintOr disjuncts -> Format.sprintf "@[%s@]" (String.concat " \\/ " (List.map string_of_constraint disjuncts))
| ConstraintImplies (lhs, rhs) -> Format.sprintf "@[%s @,=>@, %s@]" (string_of_constraint lhs) (string_of_constraint rhs)
| ConstraintExists (vs, subterm) -> Format.sprintf "@[exists %s in Events @,::@, %s@]" (String.concat ", " vs) (string_of_constraint subterm)

let rmstar = function
| Event (e,alist,se,_) -> Event (e,alist,se,StarNone)
| _ as e -> e

let star_constraint_of event_to_var lonestar event =
  let lonestar_var = List.assoc lonestar event_to_var in
  let star_var = List.assoc event event_to_var in
  match event with
  | Event (_,_,_,star) -> begin
    match star with
    | StarPlus -> ConstraintStarOrdered (lonestar_var, star_var)
    | StarMinus -> ConstraintStarOrdered (star_var, lonestar_var)
    | StarNotPlus -> ConstraintNot (ConstraintStarOrdered (lonestar_var, star_var))
    | StarNotMinus -> ConstraintNot (ConstraintStarOrdered (star_var, lonestar_var))
    | _ -> assert false (* unreachable *)
  end
  | _ -> assert false (* unreachable *)

let is_data_oracle = function
| Oracle id | OracleExists id | OracleTrue id -> id.[0] = 'D'

(* TODO: find data oracle in actuals list *)
let has_preload rules path =
  let events = events_of_path (edges_of_path rules path) in
  let reads = List.filter (function Event(e,_,_,_) -> e = "RD" | _ -> false) events in
  let data = List.map (function
    | Event(_, alist, _, _) -> List.nth alist 1 (* assumes this element is the data oracle *)
    | _ -> assert false (* unreachable *)) reads in
  (List.length data) != (List.length (nodups data))

let is_lonestar = function
| Event (_,_,_,Star) -> true
| _ -> false

let is_complete_singleton evs =
  List.length evs = 1 && ((List.nth evs 0) = EventComplete)

let starexpr_of_edgepath edgepath =
  let events = List.map events_of_eventexpr edgepath in
  let singleton_events = List.filter (fun evs -> List.length evs = 1) events in
  let events' = List.flatten singleton_events in
  let vars = List.map (fun _ -> efresh_name ()) events' in
  let event_to_var = List.combine events' vars in
  let matches = List.map (fun (ev, x) -> ConstraintMatch (x, [rmstar ev])) event_to_var in
  if List.exists is_lonestar events' then
    let lonestar, lonestar_var = (List.find (fun (ev, _) -> is_lonestar ev) event_to_var) in
    let star_ordered_events = List.filter (fun e -> e <> lonestar) events' in
    let star_constraints = List.map (star_constraint_of event_to_var lonestar) star_ordered_events in
    ConstraintExists (vars, conjunct (matches @ star_constraints))
  else
    ConstraintExists (vars, conjunct matches)

let starexpr_of_path rules accepting path =
  let edgepath = edges_of_path rules path in
  let edgeexpr = starexpr_of_edgepath edgepath in
  let final = List.hd (List.rev path) in
  let adj = G.succ rules final in
  match adj with
  | [] -> edgeexpr
  | _ ->
    let adj' = List.filter (fun s -> not (List.mem s accepting)) adj in
    let nots = List.map (fun s ->
      let path' = path @ [s] in
      let expr = starexpr_of_edgepath (edges_of_path rules path') in
      ConstraintNot expr
    ) adj' in
    conjunct (edgeexpr :: nots)

let vacuous_constraint dog path vars vacuous_state =
  let varpairs = (allpairs ([None] @ (List.map (fun x -> Some x) vars) @ [None])) in
  let state_to_vars = List.map2 (fun s from_to -> (s, from_to)) path varpairs in
  let preds = predecessors_of_state dog vacuous_state in
  let preds_in_path = List.filter (fun s -> List.mem s preds) path in
  let constraint_of state =
    let _,xexpr,_ = G.find_edge dog.rules state vacuous_state in
    let var = xfresh_name () in
    let matches = ConstraintMatch (var, events_of_eventexpr xexpr) in
    let prev, next = List.assoc state state_to_vars in
    let order = match prev, next with
      | None, None -> assert false (* unreachable *)
      | Some e1, None -> ConstraintClockOrdered (e1, var)
      | None, Some e2 -> ConstraintClockOrdered (var, e2)
      | Some e1, Some e2 ->
        (* TODO: constraint is dependent on priority of transition 
           higher priority: e1 <= var <= e2
           same   priority: e1 <= var <  e2 *)
        conjunct [ ConstraintClockOrdered (e1, var); ConstraintClockOrdered (var, e2) ]
    in
    ConstraintNot (ConstraintExists ([var], conjunct [matches; order]))
  in
  let constraints = List.map constraint_of preds_in_path in
  conjunct constraints

let progexpr_of_path dog vacuous path =
  let edgepath = edges_of_path dog.rules path in
  let events = List.map events_of_eventexpr edgepath in
  let fresh_event_vars = List.map (fun _ -> efresh_name ()) events in
  let matches = List.map2 (fun x evs -> if is_complete_singleton evs then ConstraintTrue else ConstraintMatch (x, evs)) fresh_event_vars events in
  let terms = (List.map (fun (x,y) -> ConstraintClockOrdered (x,y)) (allpairs fresh_event_vars)) in
  let path_has_complete_event = List.exists is_complete_singleton events in
  let positive_body = conjunct terms in
  let negative_body = conjunct (List.map (vacuous_constraint dog path fresh_event_vars) vacuous) in
  if path_has_complete_event then
    let complete_var = fst (List.find (fun (x, evs) -> is_complete_singleton evs) (List.combine fresh_event_vars events)) in
    let starts = take_while (fun v -> v <> complete_var) fresh_event_vars in
    ConstraintExists (fresh_event_vars, conjunct (matches @ [positive_body; ConstraintComplete (complete_var, starts); negative_body]))
  else
    ConstraintExists (fresh_event_vars, conjunct (matches @ [positive_body; negative_body]))

let constraint_of_end_state dog end_state =
  let rules = dog.rules in
  let is_path = make_path_checker rules in
  let inits = List.filter (fun init -> is_path init end_state) (dog.ls_inits @ dog.rw_inits) in
  let _ =
    assert (List.length inits == 1); (* exactly one initial state can reach end_state *)
    assert (List.mem end_state (assert_states_of dog)) (* valid trigger or accept state *)
  in
  let init = List.hd inits in
  let paths = extract_paths rules init [end_state] in
  if (List.mem init dog.ls_inits) then
    let vacuous = vacuous_states_of dog in
    let terms = List.map (progexpr_of_path dog vacuous) paths in
    disjunct terms
  else (* init in rw_inits *)
    let paths_no_preload = List.filter (fun p -> not (has_preload rules p)) paths in
    let accepting = accepting_states_of dog in
    let terms = List.map (starexpr_of_path rules accepting) paths_no_preload in
    disjunct terms

(* TODO: better to rewrite assertion without assuming structure of formula *)
let constraint_of_assert dog assertion =
  let lhs, rhs = assertion in
  let lhs_terms = List.map (constraint_of_end_state dog) lhs in
  let rhs_terms = List.map (constraint_of_end_state dog) rhs in
  ConstraintImplies (disjunct lhs_terms, disjunct rhs_terms)

let constraint_of_dog dog =
  let dog' = expand_letdefs dog in
  let asserts = dog'.asserts in
  conjunct (List.map (constraint_of_assert dog') asserts)
