open DogIR

let main () =
  try
    let lexbuf = Lexing.from_channel stdin in
    let dog = DogParser.main DogLexer.token lexbuf in
    let rules, asserts = dog in
    List.iter (fun (_,_,e) -> let _ = print_eventexpr e; print_string "\n" in ()) rules
  with End_of_file -> exit 0
      
let _ = Printexc.print main ()
