(* remove all duplicate values in l *)
let nodups l = 
  let rec aux acc = function
    | [] -> acc
    | x::xs -> if (List.mem x xs) then aux acc xs else aux (x::acc) xs
  in
  aux [] l

(* return all adjacent pairs of l *)
(* e.g., [1;2;3] -> [(1,2);(2,3)] *)
let allpairs l =
  let _ = assert (1 < List.length l) in
  let xs = List.rev (List.tl (List.rev l)) in
  let ys = List.tl l in
  List.map2 (fun x y -> (x,y)) xs ys

(* available in 4.02.0 *)
let rec pp_print_list pp_v ppf = function
  | [] -> ()
  | x::xs -> Format.fprintf ppf "@[%a;@]" pp_v x; pp_print_list pp_v ppf xs

(* cartesian product *)
(* http://stackoverflow.com/questions/10893521/how-to-take-product-of-two-list-in-ocaml *)
let cartesian l l' = 
  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)
