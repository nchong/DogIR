open DogGraph
open DogIR
open Lib

exception NotWellFormedError of string

(* Ensure every assert of the form s |-> s' uses existing states s and s' *)
let check_assert_states dog =
  let rules, asserts = dog.rules, dog.asserts in
  let assert_states = nodups (List.fold_right (fun (s, s') states -> [s;s'] @ states) asserts []) in
  let ok = ref true in
  let _ = List.iter 
    (fun s -> if (G.mem_vertex rules s) then () else (Printf.printf "Error: state '%s' used in assert not found in dog\n" s; ok := false)) assert_states in
  !ok

(* Ensure every event using @e has a matching @s *)
(* TODO: not checking load-store domain now *)
let check_matching_start_for_each_end dog =
  let rules, asserts = dog.rules, dog.asserts in
  let initial = initial_states_of dog in
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
    let paths = extract_paths rules i accepting in
    List.iter check_path paths
  ) initial in
  !ok

(* Check at most one star event per path from initial to accepting *)
(* TODO: not checking load-store domain; but possibly should check stronger
 condition that no star events appear at all in load-store domain *)
let check_at_most_one_star_per_path dog =
  let rules, asserts = dog.rules, dog.asserts in
  let initial = initial_states_of dog in
  let accepting = accepting_states_of dog in
  let ok = ref true in
  let check_path path =
    let events = events_of_path path in
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
