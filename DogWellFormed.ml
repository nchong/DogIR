open DogGraph
open DogIR

let nodups l = 
  let rec aux acc = function
    | [] -> acc
    | x::xs -> if (List.mem x xs) then aux acc xs else aux (x::acc) xs
  in
  aux [] l

exception NotWellFormedError of string

let check_assert_states (rules, asserts) =
  let assert_states = nodups (List.fold_right (fun (s, s') states -> [s;s'] @ states) asserts []) in
  let ok = ref true in
  let _ = List.iter 
    (fun s -> if (G.mem_vertex rules s) then () else (Printf.printf "Error: state '%s' used in assert not found in DOG" s; ok := false)) assert_states in
  !ok

let check_matching_start_for_each_end (rules, _) =
  let exprs = G.fold_edges_e (fun (_,expr,_) acc -> expr::acc) rules [] in
  let ends = List.filter (function | ExprEvent(Event(_,_,AtEnd,_)) -> true | _ -> false) exprs in
  (* ignore all stars when trying to find a matching @s *)
  let exprs = List.map (fun expr ->
    match expr with
    | ExprEvent(Event(e, alist, se, _)) -> ExprEvent(Event(e, alist, se, StarNone))
    | _ -> expr) exprs in
  let ok = ref true in
  let _ = List.iter (fun expr ->
    match expr with
    | ExprEvent Event (e,alist,AtEnd,_) ->
      if List.mem (ExprEvent(Event(e,alist,AtStart,StarNone))) exprs then ()
      else (Printf.printf "Error: no matching @s event for %s" (string_of_eventexpr expr); ok := false)
    | _ -> assert false (* unreachable *)
  ) ends in
  !ok

let wf dog =
  if check_assert_states dog then () else raise (NotWellFormedError "Assert expression does not use defined states");
  if check_matching_start_for_each_end dog then () else raise (NotWellFormedError "Not all @e have matching @s event")
