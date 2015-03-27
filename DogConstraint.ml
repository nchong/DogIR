open DogIR
open DogGraph
open Lib

(* Assume at most one event per eventexpr edge *)

type star_constraint =
| ConstraintTrue
| ConstraintExists of event                  (* e \in Ev *)
| ConstraintStarOrdered of event * event     (* (e1,e2) \in     so *)
| ConstraintNot of star_constraint
| ConstraintAnd of star_constraint * star_constraint
| ConstraintOr of star_constraint * star_constraint

let conjunct constraints =
  match constraints with
  | [] -> ConstraintTrue
  | c::cs -> List.fold_left (fun x expr -> ConstraintAnd (x, expr)) c cs

let rec pp_star_constraint ppf = function
| ConstraintTrue -> Format.fprintf ppf "ConstraintTrue"
| ConstraintExists e -> Format.fprintf ppf "ConstraintExists(%a)" pp_event e
| ConstraintStarOrdered (e1, e2) -> Format.fprintf ppf "ConstraintStarOrdered(%a, %a)" pp_event e1 pp_event e2
| ConstraintNot x -> Format.fprintf ppf "ConstraintNot(%a)" pp_star_constraint x
| ConstraintAnd (x1, x2) -> Format.fprintf ppf "ConstraintAnd(%a, %a)" pp_star_constraint x1 pp_star_constraint x2
| ConstraintOr (x1, x2) -> Format.fprintf ppf "ConstraintOr(%a, %a)" pp_star_constraint x1 pp_star_constraint x2

let star_constraint_of e1 e2 =
  match e1, e2 with
  | Event (_,_,_,Star), Event (_,_,_,star) -> begin
    match star with
    | StarPlus -> ConstraintStarOrdered (e1, e2)
    | StarMinus -> ConstraintStarOrdered (e2, e1)
    | StarNotPlus -> ConstraintNot (ConstraintStarOrdered (e1, e2))
    | StarNotMinus -> ConstraintNot (ConstraintStarOrdered (e2, e1))
    | _ -> ConstraintTrue
  end
  | _, _ -> ConstraintTrue

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
  | _ -> assert false (* more than one star means dog is not well-formed *)

let expr_of_edgepath edgepath =
  let events = events_of_path edgepath in
  let starts = (List.filter (function Event (e,alist,AtStart,_) -> true | _ -> false) events) in
  let exist_constraints = List.map (function Event (e,alist,AtStart,_) -> ConstraintExists (Event (e,alist,AtStart,StarNone)) | _ -> assert false (* unreachable *)) starts in
  let star_constraints =
    match lonestar_of events with
    | Some star ->
      let events' = List.filter (fun e -> e != star) events in
      List.map (fun e -> star_constraint_of star e) events'
    | None -> []
  in
  conjunct (exist_constraints @ star_constraints)

let expr_of_path rules accepting path =
  let edgepath = edges_of_path rules path in
  let edgeexpr = expr_of_edgepath edgepath in
  let final = List.hd (List.rev path) in
  let adj = G.succ rules final in
  match adj with
  | [] -> edgeexpr
  | _ ->
    let adj' = List.filter (fun s -> not (List.mem s accepting)) adj in
    let nots = List.map (fun s ->
      let path' = path @ [s] in
      let expr = expr_of_edgepath (edges_of_path rules path') in
      ConstraintNot expr
    ) adj' in
    ConstraintAnd (edgeexpr, conjunct nots)

let analyse dog =
  let rules, _ = dog in
  let initial = initial_states_of dog in
  let _ = List.iter (print_string) initial in
  let accepting = accepting_states_of dog in
  let _ = assert (List.length initial = 1) in
  let paths = extract_paths2 rules (List.nth initial 0) accepting in
  let paths' = List.filter (fun p -> not (has_preload rules p)) paths in (* no paths with preloads *)
  let constraints = List.map (expr_of_path rules accepting) paths' in
  let _ = 
    List.iter (fun path -> List.iter print_string path; print_string "\n") paths;
    print_string "\n";
    List.iter (fun path -> List.iter print_string path; print_string "\n") paths';
    print_string "\n";
    List.iter (fun x -> pp_star_constraint Format.std_formatter x; print_string "\n") constraints
  in ()
