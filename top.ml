open DogIR
open DogGraph
open Lexing

let main () =
  try
    let lexbuf = Lexing.from_channel stdin in
    let dog = try
        DogParser.main DogLexer.token lexbuf
      with DogParser.Error ->
        let lxm = lexeme lexbuf
        and start_loc = lexeme_start_p lexbuf
        (*and end_loc = lexeme_end_p lexbuf*) in
        Printf.eprintf "Parse error: file %s line %i unexpected '%s'\n" start_loc.pos_fname start_loc.pos_lnum lxm;
        exit 1
    in
    let rules, asserts = dog in
    G.iter_edges_e (fun (_,e,_) -> let _ = print_eventexpr e; print_string "\n" in ()) rules
  with End_of_file -> exit 0
      
let _ = Printexc.print main ()
