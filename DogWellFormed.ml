open DogGraph
open DogIR
open Lib

exception NotWellFormedError of string

(* Initial LS and RW states exist in the dog and are intial states *)
let check_initial_states dog =
  let rules = dog.rules in
  let initial_states = initial_states_of dog in
  let ok = ref true in
  let _ = List.iter 
    (fun s -> 
      if (G.mem_vertex rules s) then (
        if (List.mem s initial_states) then ()
        else (Printf.printf "Error: state '%s' given in INIT statement is not an initial state (has incoming edges)\n" s; ok := false);
      )
      else (Printf.printf "Error: state '%s' given in INIT statement not found in dog\n" s; ok := false);
    ) (dog.ls_inits @ dog.rw_inits)
  in
  !ok

(* Ensure every assert of the form s |-> s' uses existing states s and s' *)
let check_assert_states dog =
  let rules = dog.rules in
  let assert_states = assert_states_of dog in
  let ok = ref true in
  let _ = List.iter 
    (fun s -> if (G.mem_vertex rules s) then () else (Printf.printf "Error: state '%s' used in assert not found in dog\n" s; ok := false)) assert_states in
  !ok

(* Ensure every event using @e has a matching @s *)
let check_matching_start_for_each_end dog =
  let rules = dog.rules in
  let initial = initial_states_of dog in
  let triggering = trigger_states_of dog in
  let accepting = accepting_states_of dog in
  let ok = ref true in
  let check_path path =
    let events = events_of_path path in
    let ends = List.filter (function Event(_,_,AtEnd,_) -> true | _ -> false) events in
    let ends = nodups ends in (* should be same length / no dups expected *)
    let expected_starts = List.map (function
      | Event(e,alist,AtEnd,_) -> Event(e,alist,AtStart,StarNone)
      | _ -> assert false (* unreachable *)) ends in
    let events_ignoring_star = List.map (function
      | Event(e, alist, se, _) -> Event(e, alist, se, StarNone)
      | _ as event -> event) events in
    List.iter (fun event ->
      if List.mem event events_ignoring_star then ()
      else (Printf.printf "Error: no matching @s for %s\n" (string_of_event event); ok := false)
    ) expected_starts
  in
  let _ = List.iter (fun i ->
    let paths = extract_paths rules i (triggering @ accepting) in
    let edgepaths = List.map (edges_of_path rules) paths in
    List.iter check_path edgepaths
  ) initial in
  !ok

(* Check at most one star event per path from initial to accepting *)
let check_at_most_one_star_per_path dog =
  let rules = dog.rules in
  let initial = initial_states_of dog in
  let accepting = accepting_states_of dog in
  let ok = ref true in
  let check_path path =
    let events = events_of_path path in
    let stars = List.filter (function Event(_,_,_,Star) -> true | _ -> false) events in
    if List.length stars <= 1 then ()
    else (Printf.printf "Error: more than one star event on path\n"; ok := false)
  in
  let _ = List.iter (fun i ->
    let paths = extract_paths rules i accepting in
    let edgepaths = List.map (edges_of_path rules) paths in
    List.iter check_path edgepaths
  ) initial in
  !ok

(* No star events in load-store domain edges *)
let check_no_stars_in_load_store_domain dog =
  let rules = dog.rules in
  let ok = ref true in
  let check_event event =
    match event with
    | Event (_,_,_,star) ->
      if star == StarNone then ()
      else (Printf.printf "Error: star event [%s] appears in LS domain\n" (string_of_event event); ok := false)
    | _ -> ()
  in
  let is_path = make_path_checker rules in
  let check_edge (_,eventexpr,t) =
    if List.exists (fun init -> is_path init t) dog.ls_inits then
      let events = events_of_eventexpr eventexpr in
      List.iter check_event events
    else ()
  in
  let _ = G.iter_edges_e check_edge dog.rules in
  !ok

(* Check at most event per eventexpr edge in read-write domain *)

(* Events must not be shared by outgoing edges *)
let check_no_repeating_events dog =
  let ok = ref true in
  let check_state state =
    let edges = outcoming_edges_of_state dog state in
    let events = List.fold_right (fun e acc -> (events_of_eventexpr e) @ acc) edges [] in
    if List.length (nodups events) == List.length events then ()
    else (Printf.printf "Error: bad state '%s' has same event on different transitions\n" state; ok := false)
  in
  let _ = G.iter_vertex check_state dog.rules in
  !ok

(* Events cannot be conjuncted *)
let check_no_conjuncted_events dog =
  let ok = ref true in
  let rec check_eventexpr eventexpr =
    match eventexpr with
    | ExprNot e -> check_eventexpr e
    | ExprBool (b,e1,e2) ->
      (if b = BoolAnd then
        let events_of_e1 = events_of_eventexpr e1 in
        let events_of_e2 = events_of_eventexpr e2 in
        if events_of_e1 <> [] && events_of_e2 <> [] then
          (Printf.printf "Error: events appear in conjunct %s\n" (string_of_eventexpr eventexpr); ok := false));
      check_eventexpr e1; check_eventexpr e2
    | ExprAssign (e1, e2) -> (check_eventexpr e1; check_eventexpr e2)
    | _ -> ()
  in
  let _ = G.iter_edges_e (fun (_,eventexpr,_) -> check_eventexpr eventexpr) dog.rules in
  !ok

(* Every state appearing in an assertion is reachable by exactly one initial state *)
let check_exactly_one_initial_state dog =
  let ok = ref true in
  let rules = dog.rules in
  let is_path = make_path_checker rules in
  let initial_states = initial_states_of dog in
  let assert_states = assert_states_of dog in
  let _ =
    List.iter (fun s ->
      let init_candidates = List.filter (fun init -> is_path init s) initial_states in
      if List.length init_candidates == 1 then ()
      else (Printf.printf "Error: assert state '%s' reachable from initial states [%s]\n" s (String.concat ", " init_candidates); ok := false)
    ) assert_states
  in
  !ok

(* List of checks and accompanying error message *)
let checks = [(check_initial_states, "Initial state statement are not well-defined\n");
              (check_assert_states, "Assert expression does not use defined states\n");
              (check_matching_start_for_each_end, "Not all @e events have matching @s\n");
              (check_at_most_one_star_per_path, "Bad path with >1 star event\n");
              (check_no_stars_in_load_store_domain, "Star event appears in load-store domain\n");
              (check_no_repeating_events, "State with same event on different edges\n");
              (check_no_conjuncted_events, "Edge with conjunction of events\n");
              (check_exactly_one_initial_state, "State in assert reachable from multiple initial states\n");
             ]

let warn_all_initial_states_labelled dog =
  let initial_states = initial_states_of dog in
  let labels = dog.ls_inits @ dog.rw_inits in
  List.iter (fun s ->
    if (List.mem s labels) then ()
    else (Printf.printf "Warning: initial state '%s' is not labelled\n" s)
  )
  initial_states

let warnings = [warn_all_initial_states_labelled;]

let check_wellformed dog =
  List.iter (fun (check, msg) -> if check dog then () else raise (NotWellFormedError msg)) checks;
  List.iter (fun check -> check dog) warnings
