{
  open Generated_parser;;

  (* ocamllex is a slave to tradition, so we have to handle line breaks
     ourselves. *)
  open Lexing
  let incr_lineno lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

let digit = ['0'-'9']
let alpha = ['a'-'z'] | ['A'-'Z']
let whitespace = [' ' '\t']
let newline = '\n'
let comment = '#' [^'\n']* '\n'
let string_contents = [^'"']*

let ident_start = alpha | '_'
let ident_cont = alpha | digit | '_'

rule token = parse
  | eof                              { EOF }
  | comment                          { incr_lineno lexbuf; token lexbuf }
  | whitespace                       { token lexbuf }
  | newline                          { incr_lineno lexbuf; token lexbuf }
  | "{"                              { OPEN_BRACE }
  | "}"                              { CLOSE_BRACE }
  | "("                              { OPEN_PAREN }
  | ")"                              { CLOSE_PAREN }
  | ";"                              { SEMICOLON }
  | ","                              { COMMA }
  | "="                              { EQUALS }
  | "->"                             { ARROW }
  | "?"                              { QUESTION_MARK }
  | "~"                              { TILDE }
  | ":"                              { COLON }
  | "."                              { DOT }
  | "input"                          { KEYWORD_INPUT }
  | "fun"                            { KEYWORD_FUN }
  | "int"                            { KEYWORD_INT }
  | "true"                           { KEYWORD_TRUE }
  | "false"                          { KEYWORD_FALSE }
  | "and"                            { KEYWORD_AND }
  | "or"                             { KEYWORD_OR }
  | "xor"                            { KEYWORD_XOR }
  | "any"                            { KEYWORD_ANY }
  | "_"                              { UNDERSCORE }
  | "-"? digit+ as n                 { INT_LITERAL (int_of_string n) }
  | "+"                              { PLUS }
  | "-"                              { MINUS }
  | "*"                              { ASTERISK }
  | "/"                              { SLASH }
  | "%"                              { PERCENT }
  | "<"                              { LESS }
  | "<="                             { LESS_EQUAL }
  | "=="                             { EQUAL_EQUAL }
  | ident_start ident_cont* as s     { IDENTIFIER s }
  | ";;"                             { DOUBLE_SEMICOLON }
