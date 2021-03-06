open Arg
open DogIR
open DogGraph
open DogWellFormed
open DogInstance
open Lexing
open DogConstraint
open Printf

let dogfile = ref ""
let soinit = ref ""
let poinit = ref ""
let emitir = ref false
let emitdot = ref ""
let expand_lets = ref false
let emitfox = ref false

let ignorecmd (s:string) =
  printf "Warning: ignoring cmd arg '%s'\n" s

let options = [
  ("-i", Arg.String (fun x -> dogfile := x), "Input DOG file");
  ("-emitir", Arg.Set emitir, "Emit IR");
  ("-emitdot", Arg.String (fun x -> emitdot := x), "Dotty representation to file");
  ("-expand-lets", Arg.Set expand_lets, "Expand let definitions");
  ("-emitfox", Arg.Set emitfox, "Compute FOX");
]

let prog =
  if Array.length Sys.argv > 0 then Sys.argv.(0)
  else "dogir"

let main () =
  let _ =
    Arg.parse options ignorecmd (sprintf "Usage %s [options] -i dog" prog);
    if !dogfile = "" || not (Sys.file_exists !dogfile) then (
      eprintf "Arg error: expected input (given by -i) not found\n";
      exit 1
    )
  in
  let lexbuf = Lexing.from_channel (open_in !dogfile) in
  let dog = try
      DogParser.main DogLexer.token lexbuf
    with DogParser.Error ->
      let lxm = lexeme lexbuf
      and start_loc = lexeme_start_p lexbuf in
      eprintf "Parse error: file %s line %i unexpected '%s'\n" start_loc.pos_fname start_loc.pos_lnum lxm;
      exit 1
  in
  let dog = if (!expand_lets) then expand_letdefs dog else dog in
  let _ =
    try check_wellformed dog
    with NotWellFormedError msg ->
      eprintf "Dog well-formed error: %s\n" msg;
      exit 1
  in
  let rules = dog.rules in
  if (!emitdot <> "") then (
    dottify dog !emitdot
  );
  if !emitir then (
    G.iter_edges_e (fun (_,e,_) -> let _ = print_eventexpr e; print_string "\n" in ()) rules;
  );
  if (!emitfox) then (
    printf "Computed constraint\n";
    let fox = constraint_of_dog dog in
    printf "%s\n" (string_of_constraint fox); print_newline ();
  );
  exit 0
      
let _ = Printexc.print main ()
