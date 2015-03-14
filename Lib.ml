let nodups l = 
  let rec aux acc = function
    | [] -> acc
    | x::xs -> if (List.mem x xs) then aux acc xs else aux (x::acc) xs
  in
  aux [] l
