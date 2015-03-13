(* Dog IR *)

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

type identifier = string

type oracle =
| Oracle of identifier
| OracleExists of identifier
| OracleTrue of identifier

let tr_oracle s =
  let lastchar = s.[String.length s - 1] in
  let sym = slice s 0 (String.length s - 1) in
  match lastchar with
  | '#' -> OracleExists sym
  | '?' -> OracleTrue sym
  | _   -> Oracle s

type number = int

type startend =
| AtStart
| AtEnd

type event_symbol = identifier

type event_actual =
| EventActualOracle of oracle
| EventActualAttribute of identifier
| EventActualNot  of event_actual

type star =
| StarNone
| Star
| StarPlus
| StarMinus
| StarNotPlus
| StarNotMinus

type event =
| EventComplete
| Event of event_symbol * event_actual list * startend * star

type boolop =
| BoolOr
| BoolAnd
| BoolEq

type eventexpr =
| ExprIdentifier of identifier
| ExprOracle of oracle
| ExprNum of number
| ExprNot of eventexpr
| ExprBool of boolop * eventexpr * eventexpr
| ExprAssign of eventexpr * eventexpr
| ExprEvent of event

type state = string

type rule = state * state * eventexpr

type dog_assert = state * state

(* IR printing *)

let pp_oracle ppf = function
| Oracle s -> Format.fprintf ppf "Oracle(%s)" s
| OracleExists s -> Format.fprintf ppf "OracleExists(%s)" s
| OracleTrue s -> Format.fprintf ppf "OracleTrue(%s)" s

let rec pp_actual ppf = function
| EventActualOracle x -> Format.fprintf ppf "EventActualOracle(%a)" pp_oracle x
| EventActualAttribute x -> Format.fprintf ppf "EventActualAttribute(%s)" x
| EventActualNot x -> Format.fprintf ppf "EventActualNot(%a)" pp_actual x

let pp_startend ppf = function
| AtStart -> Format.fprintf ppf "%@s"
| AtEnd -> Format.fprintf ppf "%@e"

let pp_star ppf = function
| StarNone -> ()
| Star -> Format.fprintf ppf "*"
| StarPlus -> Format.fprintf ppf "*+"
| StarMinus -> Format.fprintf ppf "*-"
| StarNotPlus -> Format.fprintf ppf "*!-"
| StarNotMinus -> Format.fprintf ppf "*!-"

(* available in 4.02.0 *)
let rec pp_print_list pp_v ppf = function
  | [] -> ()
  | x::xs -> Format.fprintf ppf "%a " pp_v x; pp_print_list pp_v ppf xs

let pp_event ppf = function
| EventComplete -> Format.fprintf ppf "EventComplete"
| Event (e,alist,se,star) -> Format.fprintf ppf "%s(%a)%a%a" e (pp_print_list pp_actual) alist pp_startend se pp_star star

let pp_boolop ppf = function
| BoolOr -> Format.fprintf ppf "||"
| BoolAnd -> Format.fprintf ppf "&&"
| BoolEq -> Format.fprintf ppf "=="

let rec pp_eventexpr ppf = function
| ExprIdentifier x -> Format.fprintf ppf "%s" x
| ExprOracle x -> Format.fprintf ppf "%a" pp_oracle x
| ExprNum n -> Format.fprintf ppf "%d" n
| ExprNot e -> Format.fprintf ppf "!(%a)" pp_eventexpr e
| ExprBool (op,e1,e2) -> Format.fprintf ppf "(%a %a %a)" pp_eventexpr e1 pp_boolop op pp_eventexpr e2
| ExprAssign (e1,e2) -> Format.fprintf ppf "(%a := %a)" pp_eventexpr e1 pp_eventexpr e2
| ExprEvent e -> Format.fprintf ppf "%a" pp_event e

let print_eventexpr = pp_eventexpr Format.std_formatter

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

let rec string_of_oracle = function
| Oracle x -> x
| OracleExists x -> Format.sprintf "%s#" x
| OracleTrue x -> Format.sprintf "%s?" x

let rec string_of_actual = function
| EventActualOracle x -> string_of_oracle x
| EventActualAttribute x -> x
| EventActualNot x -> Format.sprintf "!%s" (string_of_actual x)

let string_of_event = function
| EventComplete -> "Complete"
| Event (e,alist,se,star) -> Format.sprintf "%s(%s)%s%s" e (String.concat ", " (List.map string_of_actual alist)) (string_of_startend se) (string_of_star star)

let rec string_of_eventexpr = function
| ExprIdentifier x -> Format.sprintf "%s" x
| ExprOracle x -> Format.sprintf "%s" (string_of_oracle x)
| ExprNum n -> Format.sprintf "%d" n
| ExprNot e -> Format.sprintf "!(%s)" (string_of_eventexpr e)
| ExprBool (op,e1,e2) -> Format.sprintf "(%s %s %s)" (string_of_eventexpr e1) (string_of_boolop op) (string_of_eventexpr e2)
| ExprAssign (e1,e2) -> Format.sprintf "(%s := %s)" (string_of_eventexpr e1) (string_of_eventexpr e2)
| ExprEvent e -> string_of_event e
