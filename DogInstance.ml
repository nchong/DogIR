open DogIR
open DogGraph

exception InstantiationError of string

let rec translate_event_actual mapping = function
| EventActualOracle x ->
  let x' =
    try
      List.assoc x mapping
    with Not_found -> raise (InstantiationError (string_of_oracle x))
  in
  EventActualAttribute x' (* EventActualOracle x' *)
| EventActualNot x -> EventActualNot (translate_event_actual mapping x)
| _ as x -> x

let translate_event mapping = function
| Event (e,alist,se,star) ->
  let alist' = List.map (translate_event_actual mapping) alist in
  Event (e,alist',se,star)
| _ as x -> x

let rec translate_expr mapping = function
| ExprNot e -> ExprNot (translate_expr mapping e)
| ExprBool (b,e1,e2) -> ExprBool(b, translate_expr mapping e1, translate_expr mapping e2)
| ExprAssign (e1, e2) -> ExprAssign(translate_expr mapping e1, translate_expr mapping e2)
| ExprEvent e -> ExprEvent (translate_event mapping e)
| _ as x -> x

let translate_edge mapping edge =
  let (s,e,s') = edge in
  (s, (translate_expr mapping e), s')

let instantiate dog mapping =
  let rules, asserts = dog in
  (CopyWithEdgeMap.map (translate_edge mapping) rules, asserts)
