{
open Lambda
open Parser_tool
open Parser
open Lexing

exception Illegal_char of string

let mk_info lexbuf =
  let cbg = !pv_col - lexeme_end lexbuf + lexeme_start lexbuf + 1 in
  {lbg = !pv_lin; cbg = cbg; lnd = !pv_lin; cnd = !pv_col}

let parse_comment () =
  let depth = ref 1 in
  let str = Bytes.of_string " " in
  let read () = if read_fun str 1 = 0 then raise Parsing.Parse_error in
  while !depth > 0 do
    read ();
    match Bytes.get str 0 with
      '(' -> read (); if Bytes.get str 0 = '*' then incr depth
    | '*' -> read (); if Bytes.get str 0 = ')' then decr depth
    | _ -> ()
  done

}

rule token = parse
  [' ' '\t' '\n' '\r']           {token lexbuf}
| '#' [^'\n']* ('\n' | eof)      {token lexbuf}
| "(*"                           {parse_comment (); token lexbuf}
| '\\'                           {Bslash(mk_info lexbuf)}
| '('                            {Lparen(mk_info lexbuf)}
| ')'                            {Rparen(mk_info lexbuf)}
| '['                            {Lbrack(mk_info lexbuf)}
| ']'                            {Rbrack(mk_info lexbuf)}
| '{'                            {Lbrace(mk_info lexbuf)}
| '}'                            {Rbrace(mk_info lexbuf)}
| '?'                            {Question(mk_info lexbuf)}
| '='                            {Equal(mk_info lexbuf)}
| ';'                            {Semicol(mk_info lexbuf)}
| ':'                            {Col(mk_info lexbuf)}
| ','                            {Comma(mk_info lexbuf)}
| '.'                            {Dot(mk_info lexbuf)}
| "=>"                           {Dot(mk_info lexbuf)}
| '*'                            {Star(mk_info lexbuf)}
| '!'                            {Exclam(mk_info lexbuf)}
| "/\\"                          {Forall(mk_info lexbuf)}
| "\\/"                          {Exists(mk_info lexbuf)}
| "->"                           {Arrow(mk_info lexbuf)}
| "case"                         {Case(mk_info lexbuf)}
| "of"                           {Of(mk_info lexbuf)}
| '"' [^'"']* '"'
                                 {String(mk_info lexbuf,
                                   String.sub (lexeme lexbuf)
                                     1 (lexeme_end lexbuf -
                                        lexeme_start lexbuf - 2))}
| [ '0'-'9' 'a'-'z' 'A'-'Z' ][ '0'-'9' 'a'-'z' 'A'-'Z' '_' ''' ]*
                                 {Ident(mk_info lexbuf,lexeme lexbuf)}
| eof                            {Eof}
| _                              {raise (Illegal_char (lexeme lexbuf))}

and resetlex = parse
  [^'\n' ';'] { resetlex lexbuf }
| '\n' { start_new := true }
| ';' { start_new := true }
| eof { start_new := true }
