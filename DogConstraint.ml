open DogIR
open DogGraph
open Lib

(* Fresh variable generator for ranging over LS events *)
let efresh_name = gen_counter "e"
(* Fresh variable generator for ranging over RW events *)
let ffresh_name = gen_counter "f"
(* Fresh variable generator for ranging over vacuous escape events *)
let xfresh_name = gen_counter "x"
(* Fresh variable generator for ranging over sync events *)
let sfresh_name = gen_counter "sync"

type dog_constraint =
| ConstraintFalse
| ConstraintTrue
| ConstraintEq of identifier * identifier
| ConstraintMatch of identifier * event list
| ConstraintComplete of identifier * identifier list
| ConstraintStarOrdered of identifier * identifier        (* (e1,e2) \in so *)
| ConstraintClockOrdered of identifier * identifier       (* (e1,e2) \in ct_leq *)
| ConstraintClockOrderedStrict of identifier * identifier (* (e1,e2) \in ct_lt *)
| ConstraintNot of dog_constraint
| ConstraintAnd of dog_constraint list
| ConstraintOr of dog_constraint list
| ConstraintImplies of dog_constraint * dog_constraint
| ConstraintSync of identifier * identifier
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

let simplify = function
  | ConstraintAnd conjuncts -> ConstraintAnd (List.filter (fun t -> t <> ConstraintTrue) conjuncts)
  | _ as f -> f

(* v,w range over identifiers *)
let rec string_of_constraint = function
| ConstraintFalse -> Format.sprintf "false"
| ConstraintTrue -> Format.sprintf "true"
| ConstraintEq (v, w) -> Format.sprintf "@[(%s = %s)@]" v w
| ConstraintMatch (v, events) -> Format.sprintf "@[(%s matches {%s})@]" v (String.concat ", " (List.map string_of_event events))
| ConstraintComplete (v, starts) -> Format.sprintf "@[isComplete(%s, {%s})@]" v (String.concat ", " starts)
| ConstraintStarOrdered (v, w) -> Format.sprintf "@[SO<=(%s,@ %s)@]" v w
| ConstraintClockOrdered (v, w) -> Format.sprintf "@[CT<=(%s,@ %s)@]" v w
| ConstraintClockOrderedStrict (v, w) -> Format.sprintf "@[CT<(%s,@ %s)@]" v w
| ConstraintNot subterm -> Format.sprintf "not(@[%s@])" (string_of_constraint subterm)
| ConstraintAnd conjuncts -> Format.sprintf "@[%s@]" (String.concat " /\\ " (List.map string_of_constraint conjuncts))
| ConstraintOr disjuncts -> Format.sprintf "@[%s@]" (String.concat " \\/ " (List.map string_of_constraint disjuncts))
| ConstraintImplies (lhs, rhs) -> Format.sprintf "@[%s @,=>@, %s@]" (string_of_constraint lhs) (string_of_constraint rhs)
| ConstraintSync (v, w) -> Format.sprintf "@[CT<=(%s, %s)@]" v w
| ConstraintExists (vs, subterm) ->
  match vs with
  | [] -> Format.sprintf "@[(%s)@]" (string_of_constraint subterm)
  | _ -> Format.sprintf "@[(exists %s in Events @,::@, %s)@]" (String.concat ", " vs) (string_of_constraint subterm)

type dog_constraint_t = {
  formula: dog_constraint;
  sync_assigns: (identifier * (identifier * number)) list;
  sync_eqs: (identifier * (identifier * number)) list;
}

let make_sync_map event_vars syncs =
  let pairs = List.combine event_vars syncs in
  let filtered = List.filter (fun (_, sync) -> sync <> None) pairs in
  let remove_some = function
    | None -> assert false (* unreachable *)
    | Some x -> x
  in
  List.map (fun (event_var, sync) -> event_var, remove_some sync) filtered

let print_sync syncs =
  String.concat "# " (List.map (fun (v, (x,n)) -> Format.sprintf "(%s, (%s,%d))" v x n) syncs)

(* RW constraint generation *)

(* TODO: find data oracle in actuals list *)
let has_preload rules path =
  let events = events_of_path (edges_of_path rules path) in
  let reads = List.filter (function Event(e,_,_,_) -> e = "RD" | _ -> false) events in
  let data = List.map (function
    | Event(_, alist, _, _) -> List.nth alist 1 (* assumes this element is the data oracle *)
    | _ -> assert false (* unreachable *)) reads in
  (List.length data) <> (List.length (nodups data))

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

let generate_rwpath_vars edgepath =
  let gather acc eventexpr =
    let events = events_of_eventexpr eventexpr in
    match List.length events with
    | 0 -> None :: acc
    | 1 ->
      let event = List.hd events in
      Some (event, ffresh_name ()) :: acc
    | _ -> assert false (* wf condition *)
  in
  List.rev (List.fold_left gather [] edgepath)

exception No_next_event

let generate_rwpath_syncs edgepath event_var_pairs =
  let var_of = function
    | None -> assert false
    | Some (_, v) -> v
  in
  let sync_vars = List.mapi (fun i opt ->
    match opt with
    | None ->
      let tail = tail_from event_var_pairs i in
      (try
        let opt' = List.find (fun x -> x <> None) tail in
        var_of opt'
      with Not_found -> raise No_next_event)
    | _ -> var_of opt
  ) event_var_pairs in
  let sync_assigns = List.map sync_assign_of_eventexpr edgepath in
  let sync_eqs = List.map sync_eq_of_eventexpr edgepath in
  let path_sync_assigns = make_sync_map sync_vars sync_assigns in
  let path_sync_eqs = make_sync_map sync_vars sync_eqs in
  path_sync_assigns, path_sync_eqs

let rmstar = function
| Event (e,alist,se,_) -> Event (e,alist,se,StarNone)
| _ as e -> e

let is_lonestar = function
| Event (_,_,_,Star) -> true
| _ -> false

let starexpr_of_edgepath edgepath =
  let event_var_pairs = generate_rwpath_vars edgepath in
  let sync_assigns, sync_eqs = generate_rwpath_syncs edgepath event_var_pairs in
  let event_to_var = remove_some (List.filter (fun x -> x <> None) event_var_pairs) in
  let events', vars  = List.split event_to_var in
  let match_constraints = List.map (fun (ev, x) -> ConstraintMatch (x, [rmstar ev])) event_to_var in
  let clock_constraints = (List.map (fun (x,y) -> ConstraintClockOrdered (x,y)) (all_adjacent_pairs vars)) in
  let formula = if List.exists is_lonestar events' then
      let lonestar, lonestar_var = (List.find (fun (ev, _) -> is_lonestar ev) event_to_var) in
      let star_ordered_events = List.filter (fun e -> e <> lonestar) events' in
      let star_constraints = List.map (star_constraint_of event_to_var lonestar) star_ordered_events in
      ConstraintExists (vars, conjunct (match_constraints @ clock_constraints @ star_constraints))
    else
      ConstraintExists (vars, conjunct (match_constraints @ clock_constraints))
  in {formula; sync_assigns; sync_eqs}

let starexpr_of_path rules accepting path =
  let edgepath = edges_of_path rules path in
  let dog_constraint = starexpr_of_edgepath edgepath in
  let final = List.hd (List.rev path) in
  let adj = G.succ rules final in
  match adj with
  | [] -> dog_constraint
  | _ ->
    let adj' = List.filter (fun s -> not (List.mem s accepting)) adj in
    (* TODO: gather these syncs too *)
    let not_constraints = List.map (fun s ->
      let path' = path @ [s] in
      let escape_constraint = starexpr_of_edgepath (edges_of_path rules path') in
      {escape_constraint with formula = ConstraintNot (escape_constraint.formula)}
    ) adj' in
    let nots = List.map (fun x -> x.formula) not_constraints in
    let formula = conjunct (dog_constraint.formula :: nots) in
    let sync_assigns = dog_constraint.sync_assigns @ 
      (List.concat (List.map (fun x -> x.sync_assigns) not_constraints))
    in
    let sync_eqs = dog_constraint.sync_eqs @ 
      (List.concat (List.map (fun x -> x.sync_eqs) not_constraints))
    in
    {formula; sync_assigns; sync_eqs}

(* LS constraint generation *)

let vacuous_constraint dog path vars vacuous_state =
  let varpairs = (all_adjacent_pairs ([None] @ (List.map (fun x -> Some x) vars) @ [None])) in
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

let generate_lspath_syncs edgepath vars =
  let sync_assigns = List.map sync_assign_of_eventexpr edgepath in
  let sync_eqs = List.map sync_eq_of_eventexpr edgepath in
  let path_sync_assigns = make_sync_map vars sync_assigns in
  let path_sync_eqs = make_sync_map vars sync_eqs in
  path_sync_assigns, path_sync_eqs

let is_complete_singleton evs =
  List.length evs = 1 && ((List.nth evs 0) = EventComplete)

let progexpr_of_path dog vacuous path =
  let edgepath = edges_of_path dog.rules path in
  let events = List.map events_of_eventexpr edgepath in
  let vars = List.map (fun _ -> efresh_name ()) events in
  let sync_assigns, sync_eqs = generate_lspath_syncs edgepath vars in
  let matches = List.map2 (fun x evs -> if is_complete_singleton evs then ConstraintTrue else ConstraintMatch (x, evs)) vars events in
  let terms = (List.map (fun (x,y) -> ConstraintClockOrdered (x,y)) (all_adjacent_pairs vars)) in
  let path_has_complete_event = List.exists is_complete_singleton events in
  let positive_body = conjunct terms in
  let negative_body = conjunct (List.map (vacuous_constraint dog path vars) vacuous) in
  let formula = if path_has_complete_event then
      let complete_var = fst (List.find (fun (x, evs) -> is_complete_singleton evs) (List.combine vars events)) in
      let starts = take_while (fun v -> v <> complete_var) vars in
      ConstraintExists (vars, conjunct (matches @ [positive_body; ConstraintComplete (complete_var, starts); negative_body]))
    else
      ConstraintExists (vars, conjunct (matches @ [positive_body; negative_body]))
  in {formula; sync_assigns; sync_eqs}

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
  let dog_constraints = if (List.mem init dog.ls_inits) then
      let vacuous = vacuous_states_of dog in
      List.map (progexpr_of_path dog vacuous) paths
    else (* init in rw_inits *)
      let paths_no_preload = List.filter (fun p -> not (has_preload rules p)) paths in
      let accepting = accepting_states_of dog in
      List.map (starexpr_of_path rules accepting) paths_no_preload
  in
  let terms = List.map (fun x -> x.formula) dog_constraints in
  let sync_assigns = List.concat (List.map (fun x -> x.sync_assigns) dog_constraints) in
  let sync_eqs = List.concat (List.map (fun x -> x.sync_eqs) dog_constraints) in
  {formula=disjunct terms; sync_assigns=sync_assigns; sync_eqs=sync_eqs}

let hoist_sync_vars formula (syncs:(identifier list * identifier) list) =
  let sync_var_map = List.flatten (List.map (fun (xs, y) ->
    let s = sfresh_name () in
    (y,s) :: (List.map (fun x -> (x,s)) xs)) syncs)
  in
  let sync_assigns = List.flatten (List.map fst syncs) in
  let sync_equalities = List.map snd syncs in
  let rec hoist = function
    | ConstraintNot subformula -> ConstraintNot (hoist subformula)
    | ConstraintAnd conjuncts -> ConstraintAnd (List.map hoist conjuncts)
    | ConstraintOr disjuncts -> ConstraintOr (List.map hoist disjuncts)
    | ConstraintImplies (lhs, rhs) -> ConstraintImplies (hoist lhs, hoist rhs)
    | ConstraintExists (vs, subterm) ->
      let assigns = List.filter (fun v -> List.mem v sync_assigns) vs in
      let eqs, vs' = List.partition (fun v -> List.mem v sync_equalities) vs in
      let subterm' = hoist subterm in
      let assign_terms = List.map (fun v -> ConstraintEq (v, List.assoc v sync_var_map)) assigns in
      let eq_terms = List.map (fun v -> ConstraintSync (List.assoc v sync_var_map, v)) eqs in
      let formula = simplify (conjunct (subterm' :: (assign_terms @ eq_terms))) in
      ConstraintExists (vs', formula)
    | _ as formula -> formula
  in
  ConstraintExists (List.sort compare (nodups (List.map snd sync_var_map @ sync_equalities)), hoist formula)

(* TODO: better to rewrite assertion without assuming structure of formula *)
let constraint_of_assert dog assertion =
  let lhs, rhs = assertion in
  let lhs_constraints = List.map (constraint_of_end_state dog) lhs in
  let rhs_constraints = List.map (constraint_of_end_state dog) rhs in
  let lhs_formula = disjunct (List.map (fun x -> x.formula) lhs_constraints) in
  let rhs_formula = disjunct (List.map (fun x -> x.formula) rhs_constraints) in
  let formula = ConstraintImplies (lhs_formula, rhs_formula) in
  let sync_assigns =
    (List.concat (List.map (fun x -> x.sync_assigns) lhs_constraints)) @
    (List.concat (List.map (fun x -> x.sync_assigns) rhs_constraints))
  in
  let sync_eqs =
    (List.concat (List.map (fun x -> x.sync_eqs) lhs_constraints)) @
    (List.concat (List.map (fun x -> x.sync_eqs) rhs_constraints))
  in
  let _ =
    Printf.printf "sync_assigns = [%s]\n" (print_sync sync_assigns);
    Printf.printf "sync_eqs     = [%s]\n" (print_sync sync_eqs);
  in
  let syncs = List.map (fun (end_sync_var, (sync_var, num)) ->
    let matches = List.find_all (fun (start_sync_var, (sync_var', num')) -> sync_var = sync_var' && num = num') sync_assigns in
    let start_sync_vars = List.map (fun (start_sync_var, (_, _)) -> start_sync_var) matches in
    let _ = assert (List.length start_sync_vars > 0) in
    (start_sync_vars, end_sync_var)
  ) sync_eqs
  in
  hoist_sync_vars formula syncs

let constraint_of_dog dog =
  let dog' = expand_letdefs dog in
  let asserts = dog'.asserts in
  conjunct (List.map (constraint_of_assert dog') asserts)
