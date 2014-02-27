(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*            This file is part of the DpdGraph tools.                        *)
(*   Copyright (C) 2009-2013 Anne Pacalet (Anne.Pacalet@free.fr)           *)
(*             ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~                                *)
(*        This file is distributed under the terms of the                     *)
(*         GNU Lesser General Public License Version 2.1                      *)
(*        (see the enclosed LICENSE file for mode details)                    *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

{
  module P = Dpd_parse (* tokens *)
  module C = Dpd_compute

let new_line lexbuf = (* in ocaml-3.11.0 but not before... *)
  let lcp = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { lcp with
    Lexing.pos_lnum = lcp.Lexing.pos_lnum + 1;
    Lexing.pos_bol = lcp.Lexing.pos_cnum;
  }

}

let blank = [' ' '\t' ]
let newline = ['\n']
let letter =  ['a'-'z']|['A'-'Z']
let digit =  ['0'-'9']
let number = ['0'-'9']+
let first_letter = letter | '_'
let other_letter = first_letter | digit
let ident = first_letter other_letter*

rule token = parse
  | blank+                    { token lexbuf }     (* skip blanks *)
  | newline                   { new_line lexbuf; token lexbuf }
  | "/*"                      { let _ = comment lexbuf in token lexbuf }
  | "//" [^'\n']* newline     { token lexbuf }

  | "N:"                      { P.NODE }
  | "E:"                      { P.EDGE }
  | '['                       { P.LBRACKET }
  | ']'                       { P.RBRACKET }

  | ","                       { P.COMMA }
  | ";"                       { P.SEMICOL }
  | "="                       { P.EQUAL }

  | ident as s            { P.IDENT s }
  | number as s           { P.NUM (int_of_string s) }

  | '"' ([^'"']+ as str) '"' { P.STRING (str)}

  | eof               { P.EOF }
  | _               { let str    = String.escaped (Lexing.lexeme lexbuf) in
                        Format.printf "illegal character: '%s' at %a\n"
                          str C.pp_lex_pos (Lexing.lexeme_start_p lexbuf);
                        raise (C.Error "lexical error")
                    }

and comment = parse
        "*/"                  { () }
  |     newline                  { new_line lexbuf; comment lexbuf }
  |     _                     { comment lexbuf }
  | eof { raise (C.Error "lexical error : unterminated comment") }

{
  let read filename =
    try
      let buf_in = open_in filename in
      let lexbuf = Lexing.from_channel buf_in in
      let init_pos = lexbuf.Lexing.lex_curr_p in
        lexbuf.Lexing.lex_curr_p <- 
        { init_pos with Lexing.pos_fname = filename };
      let info = P.graph token lexbuf in
        close_in buf_in;
        info
    with Sys_error msg -> raise (C.Error msg)

}

