open DogIR
open DogGraph
open DogWellFormed
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
    let _ = check_wellformed dog in
    dottify dog "mygraph.dot";
  with End_of_file -> exit 0
      
let _ = Printexc.print main ()
