(* remove all duplicate values in l *)
let nodups l = 
  let rec aux acc = function
    | [] -> acc
    | x::xs -> if (List.mem x xs) then aux acc xs else aux (x::acc) xs
  in
  aux [] l

(* return all adjacent pairs of l *)
(* e.g., [1;2;3] -> [(1,2);(2,3)] *)
let all_adjacent_pairs l =
  if List.length l <= 1 then
    []
  else
    let xs = List.rev (List.tl (List.rev l)) in
    let ys = List.tl l in
    List.map2 (fun x y -> (x,y)) xs ys

(* available in 4.02.0 *)
let rec pp_print_list ?(sep=";") pp_v ppf = function
  | [] -> ()
  | x::xs -> Format.fprintf ppf "@[%a%s@]" pp_v x sep; pp_print_list ~sep pp_v ppf xs

(* cartesian product *)
(* e.g., cartesian [1;2;3] [a;b] -> [(1,a);(1,b);(2,a);(2,b);(3,a);(3,b)] *)
(* http://stackoverflow.com/questions/10893521/how-to-take-product-of-two-list-in-ocaml *)
let cartesian l l' = 
  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)

(* fresh counter generator *)
(* If xfresh = gen_counter "x" then each xfresh() call gives fresh vars x0, x1, ... *)
let gen_counter prefix =
  let idx = ref 0 in
  let fresh () =
    let x = String.concat "" [ prefix; (string_of_int !idx) ] in
    let _ = idx := !idx + 1 in
    x
  in
  fresh

(* accumulate while a elements satisfy a predicate *)
(* e.g., take_while (fun x -> x < 3) [0;1;2;3;0] -> [0;1;2] *)
let take_while pred xs =
  let rec aux acc = function
    | [] -> acc
    | x::xs -> if pred x then aux (x::acc) xs else acc
  in
  List.rev (aux [] xs)

(* filter option list by removing contents of Some _ *)
(* e.g., remove_some [Some 0; Some 1; Some 2] -> [0;1;2] *)
let remove_some xs =
  let f = function
    | None -> raise (Invalid_argument "remove_some") 
    | Some x -> x
  in
  List.map f xs

(* return the remainder of a list from a given index *)
(* e.g. tail_from [0;1;2;3] 1 -> [1;2;3] *)
let tail_from xs n =
  let rec aux acc i =
    if i >= List.length xs then acc
    else
      let acc' = if i < n then acc else (List.nth xs i)::acc in
      aux acc' (i+1)
  in
  List.rev (aux [] 0)
