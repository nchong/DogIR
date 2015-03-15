open DogGraph
open DogIR
open Lib

exception NotWellFormedError of string

(* Ensure every assert of the form s |-> s' uses existing states s and s' *)
let check_assert_states (rules, asserts) =
  let assert_states = nodups (List.fold_right (fun (s, s') states -> [s;s'] @ states) asserts []) in
  let ok = ref true in
  let _ = List.iter 
    (fun s -> if (G.mem_vertex rules s) then () else (Printf.printf "Error: state '%s' used in assert not found in DOG" s; ok := false)) assert_states in
  !ok

(* Ensure every event using @e has a matching @s *)
(* TODO: more than one event per edge is possible *)
let check_matching_start_for_each_end (rules, _) =
  let exprs = G.fold_edges_e (fun (_,expr,_) acc -> expr::acc) rules [] in
  let ends = List.filter (function ExprEvent(Event(_,_,AtEnd,_)) -> true | _ -> false) exprs in
  let ends = nodups ends in
  let expected_starts = List.map (function
    | ExprEvent(Event(e,alist,AtEnd,_)) -> ExprEvent(Event(e,alist,AtStart,StarNone))
    | _ -> assert false (* unreachable *)) ends in
  let exprs_ignoring_star = List.map (fun expr ->
    match expr with
    | ExprEvent(Event(e, alist, se, _)) -> ExprEvent(Event(e, alist, se, StarNone))
    | _ -> expr) exprs in
  let ok = ref true in
  let _ = List.iter (fun expr ->
      if List.mem expr exprs_ignoring_star then ()
      else (Printf.printf "Error: no matching @s event for %s" (string_of_eventexpr expr); ok := false)
  ) expected_starts in
  !ok

(* Check at most one star event per path from initial to accepting *)
let check_at_most_one_star_per_path dog =
  let rules, asserts = dog in
  let initial = initial_states_of dog in
  let accepting = accepting_states_of dog in
  let ok = ref true in
  let check_path path =
    let events = List.fold_right (fun expr acc -> (events_of_eventexpr expr) @ acc) path [] in
    let stars = List.filter (function Event(_,_,_,Star) -> true | _ -> false) events in
    if List.length stars <= 1 then ()
    else (Printf.printf "More than one star event on path"; ok := false)
  in
  let _ = List.iter (fun i ->
    let paths = extract_paths rules i accepting in
    List.iter check_path paths
  ) initial in
  !ok

(* List of checks and accompanying error message *)
let checks = [(check_assert_states, "Assert expression does not use defined states");
              (check_matching_start_for_each_end, "Not all @e events have matching @s");
              (check_at_most_one_star_per_path, "Bad path with >1 star event"); ]

let check_wellformed dog =
  List.iter (fun (check, msg) -> if check dog then () else raise (NotWellFormedError msg)) checks
