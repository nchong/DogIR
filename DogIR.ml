(* Dog IR *)
open Lib

type number = int
type identifier = string

type oracle =
| Oracle of identifier       (* e.g., A0 *)
| OracleExists of identifier (* e.g., A# *)
| OracleTrue of identifier   (* e.g., A? *)

type startend =
| AtStart
| AtEnd

type event_symbol = identifier

type event_formal =
| EventFormalOracle of oracle
| EventFormalAttribute of identifier
| EventFormalNot of event_formal

type star =
| StarNone
| Star
| StarPlus
| StarMinus
| StarNotPlus
| StarNotMinus

type event =
| EventComplete
| Event of event_symbol * event_formal list * startend * star

type boolop =
| BoolOr
| BoolAnd
| BoolEq

type arithop =
| ArithPlus
| ArithMinus

type eventexpr =
| ExprSelector of identifier
| ExprIdentifier of identifier
| ExprNum of number
| ExprNot of eventexpr
| ExprBool of boolop * eventexpr * eventexpr
| ExprAssign of eventexpr * eventexpr
| ExprEvent of event
(* ExprArith of arithop * eventexpr * eventexpr *)

type letdef = identifier * eventexpr

type state = string

type rule = state * state * eventexpr

type dog_assert = state list * state list

(* Helpers *)

let rec substitute (find_id, replace_expr) eventexpr =
  let aux = substitute (find_id, replace_expr) in
  match eventexpr with
  | ExprSelector _ -> eventexpr
  | ExprIdentifier id -> if id = find_id then replace_expr else eventexpr
  | ExprNum _ -> eventexpr
  | ExprNot e -> ExprNot (aux e)
  | ExprBool (b,e1,e2) -> ExprBool (b, (aux e1), (aux e2))
  | ExprAssign (e1, e2) -> ExprAssign ((aux e1), (aux e2))
  | ExprEvent ev -> eventexpr (* find_id cannot appear in ev *)

let events_of_eventexpr ev =
  let rec aux ev acc =
    match ev with
    | ExprSelector _ | ExprIdentifier _ | ExprNum _ -> acc
    | ExprNot e -> aux e acc
    | ExprBool (_,e1,e2) | ExprAssign (e1,e2) -> aux e1 (aux e2 acc)
    | ExprEvent e -> e::acc
  in
  aux ev []

let is_identifier = function
| ExprIdentifier _ -> true
| _ -> false

let is_num = function
| ExprNum _ -> true
| _ -> false

let sync_assign_of_eventexpr eventexpr =
  let rec aux ev acc =
    match ev with
    | ExprAssign (ExprIdentifier x, ExprNum n) -> (x,n)::acc
    | ExprSelector _ | ExprAssign (_, _) | ExprIdentifier _ | ExprNum _ | ExprNot _ | ExprEvent _ -> acc
    | ExprBool (_,e1,e2) -> aux e1 (aux e2 acc)
  in
  let sync_assigns = aux eventexpr [] in
  match List.length sync_assigns with
  | 0 -> None
  | 1 -> Some (List.hd sync_assigns)
  | _ -> assert false (* wf condition *)

let sync_eq_of_eventexpr = function
  | ExprBool (b,e1,e2) ->
    (match b, e1, e2 with
    | BoolEq, ExprIdentifier x, ExprNum n -> Some (x,n)
    | _, _, _ -> None)
  | _ -> None

(* slice string s from index [n:m] *)
let slice s n m =
  assert (n <= m);
  assert (0 <= n); assert (n <= String.length s);
  assert (0 <= m); assert (m <= String.length s);
  let rec aux acc i =
    if i == m then acc
    else aux ((Char.escaped s.[i]) :: acc) (i+1)
  in
  String.concat "" (List.rev (aux [] n))

let tr_oracle s =
  let lastchar = s.[String.length s - 1] in
  let sym = slice s 0 (String.length s - 1) in
  match lastchar with
  | '#' -> OracleExists sym
  | '?' -> OracleTrue sym
  | _   -> Oracle s

let tr_dog_assert lhs_and_states rhs_or_states =
  (lhs_and_states, rhs_or_states)

(* IR pretty printing *)

let pp_string ppf s =
  Format.fprintf ppf "\"%s\"" s

let pp_oracle ppf = function
| Oracle s -> Format.fprintf ppf "Oracle(@[%a@])" pp_string s
| OracleExists s -> Format.fprintf ppf "OracleExists(@[%a@])" pp_string s
| OracleTrue s -> Format.fprintf ppf "OracleTrue(@[%a@])" pp_string s

let rec pp_actual ppf = function
| EventFormalOracle x -> Format.fprintf ppf "EventFormalOracle(@[%a@])" pp_oracle x
| EventFormalAttribute x -> Format.fprintf ppf "EventFormalAttribute(@[%a@])" pp_string x
| EventFormalNot x -> Format.fprintf ppf "EventFormalNot(@[%a@])" pp_actual x

let pp_startend ppf = function
| AtStart -> Format.fprintf ppf "AtStart"
| AtEnd -> Format.fprintf ppf "AtEnd"

let pp_star ppf = function
| StarNone -> Format.fprintf ppf "StarNone"
| Star -> Format.fprintf ppf "Star"
| StarPlus -> Format.fprintf ppf "StarPlus"
| StarMinus -> Format.fprintf ppf "StarMinus"
| StarNotPlus -> Format.fprintf ppf "StarNotPlus"
| StarNotMinus -> Format.fprintf ppf "StarNotMinus"

let pp_event ppf = function
| EventComplete -> Format.fprintf ppf "EventComplete"
| Event (e,alist,se,star) -> Format.fprintf ppf "Event(@[%a,@ [%a],@ %a,@ %a@])" pp_string e (pp_print_list pp_actual) alist pp_startend se pp_star star

let pp_boolop ppf = function
| BoolOr -> Format.fprintf ppf "BoolOr"
| BoolAnd -> Format.fprintf ppf "BoolAnd"
| BoolEq -> Format.fprintf ppf "BoolEq"

let rec pp_eventexpr ppf = function
| ExprSelector x -> Format.fprintf ppf "ExprSelector(@[%a@])" pp_string x
| ExprIdentifier x -> Format.fprintf ppf "ExprIdentifier(@[%a@])" pp_string x
| ExprNum n -> Format.fprintf ppf "ExprNum(@[%d@])" n
| ExprNot e -> Format.fprintf ppf "ExprNot(@[%a@])" pp_eventexpr e
| ExprBool (op,e1,e2) -> Format.fprintf ppf "ExprBool(@[%a,@ %a,@ %a@])" pp_boolop op pp_eventexpr e1 pp_eventexpr e2
| ExprAssign (e1,e2) -> Format.fprintf ppf "ExprAssign(@[%a,@ %a@])" pp_eventexpr e1 pp_eventexpr e2
| ExprEvent e -> Format.fprintf ppf "ExprEvent(@[%a@])" pp_event e

let print_eventexpr = pp_eventexpr Format.std_formatter

(* IR to string *)

let string_of_boolop = function
| BoolOr -> "||"
| BoolAnd -> "&&"
| BoolEq -> "=="

let string_of_oracle = function
| Oracle x -> Format.sprintf "%s" x
| OracleExists x -> Format.sprintf "%s#" x
| OracleTrue x -> Format.sprintf "%s?#" x

let string_of_startend = function
| AtStart -> "@s"
| AtEnd   -> "@e"

let string_of_star = function
| StarNone -> ""
| Star -> "*"
| StarPlus -> "*+"
| StarMinus -> "*-"
| StarNotPlus -> "*!+"
| StarNotMinus -> "*!-"

let rec string_of_actual = function
| EventFormalOracle x -> string_of_oracle x
| EventFormalAttribute x -> x
| EventFormalNot x -> Format.sprintf "!%s" (string_of_actual x)

let string_of_event = function
| EventComplete -> "Complete"
| Event (e,alist,se,star) -> Format.sprintf "%s(%s)%s%s" e (String.concat ", " (List.map string_of_actual alist)) (string_of_startend se) (string_of_star star)

let rec string_of_eventexpr = function
| ExprSelector x -> Format.sprintf "%s" x
| ExprIdentifier x -> Format.sprintf "%s" x
| ExprNum n -> Format.sprintf "%d" n
| ExprNot e -> Format.sprintf "!(%s)" (string_of_eventexpr e)
| ExprBool (op,e1,e2) -> Format.sprintf "(%s %s %s)" (string_of_eventexpr e1) (string_of_boolop op) (string_of_eventexpr e2)
| ExprAssign (e1,e2) -> Format.sprintf "(%s := %s)" (string_of_eventexpr e1) (string_of_eventexpr e2)
| ExprEvent e -> string_of_event e

let string_of_dog_assert assertion =
  let lhs, rhs = assertion in
  Format.sprintf "%s |-> %s" (String.concat " \\/ " lhs) (String.concat " /\\ " rhs)
