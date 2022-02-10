{
open Core
open Parser

}

let ident = [^ '(' ')' '[' ']' '{' '}' '\\' ':' ',' ' ' '\t' '\n' '^' '|' '?' '.' ]+
let whitespace = [' ' '\t' '\r']

rule initial = parse
  | whitespace+ { initial lexbuf }
  | '\n' { Lexing.new_line lexbuf; initial lexbuf }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LSQAURE }
  | ']' { RSQUARE }
  | '{' { LCURLY }
  | '}' { RCURLY }
  | '|' { BAR }
  | '.' { DOT }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | '_' { UNDERBAR }
  | '/' { FSLASH }
  | '?' { HOLE }
  | '\\' | "λ" { LAMBDA }
  | "->" | "→" { R_ARROW }
  | "=>" | "⇒" { R_EQ_ARROW }
  | "sig" { SIG }
  | "struct" { STRUCT }
  | "Type" { TYPE }
  | "Sub" { SUB }
  | "elim" { ELIM }
  | "def" { DEF }
  | "axiom" { AXIOM }
  | "import" { IMPORT }
  | "data" { DATA }
  | "{-" { comment 1 lexbuf }
  | "-}" { failwith "Unbalanced comments" }
  | "--" { comment_line lexbuf }
  | ident as x { IDENT x }
  | eof { EOF }
  | _ as x { failwith ("illegal char: " ^ (Char.to_string x)) }

and comment nesting = parse
  | '\n' { Lexing.new_line lexbuf; comment nesting lexbuf }
  | "{-" { comment (nesting + 1) lexbuf }
  | "-}" { match nesting - 1 with | 0 -> initial lexbuf | n' -> comment n' lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment nesting lexbuf }

and comment_line = parse
  | '\n' { Lexing.new_line lexbuf; initial lexbuf }
  | eof { failwith "Reached EOF in comment" }
  | _ { comment_line lexbuf }