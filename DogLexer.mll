{
open DogIR
open DogParser
open Lexing
exception Error of string * position
let error msg lexbuf = raise (Error (msg,lexbuf.lex_curr_p ))
}

let digit = [ '0'-'9' ]
let lower = [ 'a'-'z' ]
let upper = [ 'A'-'Z' ]
let alpha = (lower | upper)
let num = digit+
let name  = alpha (alpha | digit| '_' | '-')*
let eventsym = (upper)+
let oracle = (upper)+ (digit+ | '#' | '?')

rule skip_comment i = parse 
  | '\n' { skip_comment i lexbuf }   
  | "(*" { skip_comment (i+1) lexbuf }
  | "*)" { if i > 1 then skip_comment (i-1) lexbuf}
  | eof { error "eof in skip_comment" lexbuf }
  | _ { skip_comment i lexbuf}

and token = parse
| [' ''\t''\r']   { token lexbuf }
| "(*"            { skip_comment 1 lexbuf; token lexbuf  }
| '\n'            { token lexbuf }
| "!"             { BANG }
| "("             { LPAR }
| ")"             { RPAR }
| ":="            { ASSIGN }
| "||"            { OR }
| "&&"            { AND }
| "=="            { EQ }
| "COMPLETE"      { COMPLETE }
| "@s"            { ATSTART }
| "@e"            { ATEND }
| "*"             { STAR }
| "+"             { PLUS }
| "-"             { MINUS }
| ";"             { SEMI }
| ","             { COMMA }
| "ASSERT"        { ASSERT }
| "|->"           { IMPLIES }
| "->"            { ARROW }
| ":"             { COLON }
| oracle as x     { ORACLE x }
| num as x        { NUM (int_of_string x) }
| eventsym as x   { EVENTSYM x }
| name as x       { NAME x }
| eof { EOF }
| ""  { error "Dog lexer" lexbuf }

{
let token lexbuf =
  let tok = token lexbuf in
(*let _ = Printf.eprintf "Lexed '%s'\n" (lexeme lexbuf) in*)
  tok
}
