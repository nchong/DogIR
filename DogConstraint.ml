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
| ConstraintStarOrdered of event * event                  (* (e1,e2) \in so *)
| ConstraintClockOrdered of identifier * identifier       (* (e1,e2) \in ct_leq *)
| ConstraintClockOrderedStrict of identifier * identifier (* (e1,e2) \in ct_lt *)
| ConstraintNot of dog_constraint
| ConstraintAnd of dog_constraint list
| ConstraintOr of dog_constraint list
| ConstraintImplies of dog_constraint * dog_constraint
(* \exists e0 e1 ... \in Ev :: (e0 MATCHES E0) /\ (e1 MATCHES E1) /\ ... /\ RestOfConstraint *)
| ConstraintPattern of (identifier * event list) list * dog_constraint 
| ConstraintComplete of identifier * identifier list

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

let pp_exists ppf (id, evs) =
  Format.fprintf ppf "(%a,@ %a)" pp_string id (pp_print_list pp_event) evs

let string_of_exist (id, evs) =
  Format.sprintf "@[(%s MATCHES {%s})@]" id (String.concat ", " (List.map string_of_event evs))

let rec string_of_constraint = function
| ConstraintFalse -> Format.sprintf "FALSE"
| ConstraintTrue -> Format.sprintf "TRUE"
| ConstraintStarOrdered (e1, e2) -> Format.sprintf "@[(%s,@ %s) IN SO@]" (string_of_event e1) (string_of_event e2)
| ConstraintClockOrdered (x1, x2) -> Format.sprintf "@[CT<=(%s,@ %s)@]" x1 x2
| ConstraintClockOrderedStrict (x1, x2) -> Format.sprintf "@[CT<(%s,@ %s)@]" x1 x2
| ConstraintNot c -> Format.sprintf "NOT(@[%s@])" (string_of_constraint c)
| ConstraintAnd cs -> Format.sprintf "(@[%s@])" (String.concat " /\\ " (List.map string_of_constraint cs))
| ConstraintOr cs -> Format.sprintf "(@[%s@])" (String.concat " \\/ " (List.map string_of_constraint cs))
| ConstraintImplies (lhs, rhs) -> Format.sprintf "(@[%s => %s@])" (string_of_constraint lhs) (string_of_constraint rhs)
| ConstraintPattern (exists, c) -> Format.sprintf "(@[EXISTS %s :: %s@])" (String.concat " " (List.map string_of_exist exists)) (string_of_constraint c)
| ConstraintComplete (complete_event, starts) -> Format.sprintf "(@[ISCOMPLETE(%s, %s@)])" complete_event (String.concat " " starts)

let rmstar = function
| Event (e,alist,se,_) -> Event (e,alist,se,StarNone)
| _ as e -> e

let star_constraint_of e1 e2 =
  let e1', e2' = rmstar e1, rmstar e2 in
  match e1, e2 with
  | Event (_,_,_,Star), Event (_,_,_,star) -> begin
    match star with
    | StarPlus -> ConstraintStarOrdered (e1', e2')
    | StarMinus -> ConstraintStarOrdered (e2', e1')
    | StarNotPlus -> ConstraintNot (ConstraintStarOrdered (e1', e2'))
    | StarNotMinus -> ConstraintNot (ConstraintStarOrdered (e2', e1'))
    | _ -> assert false (* unreachable *)
  end
  | _, _ -> assert false (* unreachable *)

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

let lonestar_of edgepath =
  let stars = List.filter is_lonestar edgepath in
  match List.length stars with
  | 0 -> None
  | 1 -> Some (List.hd stars)
  | _ -> assert false (* more than one star means dog is not well-formed (check_at_most_one_star_per_path) *)

let is_complete_singleton evs =
  List.length evs = 1 && ((List.nth evs 1) = EventComplete)

let starexpr_of_edgepath edgepath =
  let events = List.map events_of_eventexpr edgepath in
  let fresh_event_vars = List.map (fun _ -> efresh_name ()) events in
  let matches = List.map2 (fun x evs -> (x, evs)) fresh_event_vars events in
  let all_events = events_of_path edgepath in
  let star_constraints =
    match lonestar_of all_events with
    | Some star ->
      let events' = List.filter (fun e -> e != star) all_events in
      List.map (fun e -> star_constraint_of star e) events'
    | None -> []
  in
  ConstraintPattern (matches, conjunct star_constraints)

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
    let exists = (var, events_of_eventexpr xexpr) in
    let prev, next = List.assoc state state_to_vars in
    let po = match prev, next with
      | None, None -> assert false (* unreachable *)
      | Some e1, None -> ConstraintClockOrdered (e1, var)
      | None, Some e2 -> ConstraintClockOrdered (var, e2)
      | Some e1, Some e2 ->
        (* TODO: constraint is dependent on priority of transition 
           higher priority: e1 <= var <= e2
           same   priority: e1 <= var <  e2 *)
        conjunct [ ConstraintClockOrdered (e1, var); ConstraintClockOrdered (var, e2) ]
    in
    (exists, po)
  in
  let constraints = List.map constraint_of preds_in_path in
  let exists = List.map (fun (e,_) -> e) constraints in
  let pos = List.map (fun (_,p) -> p) constraints in
  ConstraintNot (ConstraintPattern (exists, (conjunct pos)))

let progexpr_of_path dog vacuous path =
  let edgepath = edges_of_path dog.rules path in
  let events = List.map events_of_eventexpr edgepath in
  let fresh_event_vars = List.map (fun _ -> efresh_name ()) events in
  let matches = List.map2 (fun x evs -> (x, evs)) fresh_event_vars events in
  let terms = (List.map (fun (x,y) -> ConstraintClockOrdered (x,y)) (allpairs fresh_event_vars)) in
  let positive_body = conjunct terms in
  let negative_body = conjunct (List.map (vacuous_constraint dog path fresh_event_vars) vacuous) in
  ConstraintPattern (matches, conjunct [positive_body; negative_body])

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
