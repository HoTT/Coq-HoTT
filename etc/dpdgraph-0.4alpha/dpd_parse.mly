%{

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*            This file is part of the DpdGraph tools.                        *)
(*   Copyright (C) 2009-2013 Anne Pacalet (Anne.Pacalet@free.fr)           *)
(*             ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~                                *)
(*        This file is distributed under the terms of the                     *)
(*         GNU Lesser General Public License Version 2.1                      *)
(*        (see the enclosed LICENSE file for mode details)                    *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let g = ref (Dpd_compute.G.create ())

let pp_lex_inter fmt (p1, p2) =
  Format.fprintf fmt "between %a and %a" 
    Dpd_compute.pp_lex_pos p1 Dpd_compute.pp_lex_pos p2

%}

%token <string> IDENT
%token <string> STRING
%token <int> NUM
%token LBRACKET RBRACKET
%token NODE EDGE EQUAL COMMA SEMICOL EOF

%left LBRACKET
%nonassoc IDENT

%type <Dpd_compute.t_obj list> graph
%start graph
%%

graph : obj_list EOF { $1 }

obj_list :
    | obj { [$1] }
    | obj obj_list { $1::$2 }


obj :
    | node SEMICOL { $1 }
    | edge SEMICOL { $1 }
    | error { Format.printf "Error %a\n"
              pp_lex_inter ((symbol_start_pos()), (symbol_end_pos()));
            raise (Dpd_compute.Error "parse error")
          }

node : NODE NUM STRING opt_attribs { Dpd_compute.N ($2, $3, $4) }

edge : EDGE NUM NUM opt_attribs { Dpd_compute.E ($2, $3, $4) }

opt_attribs :
    | /* empty */ { [] }
    | LBRACKET attribs RBRACKET { $2 }

attribs :
    | /* empty */ { [] }
    | attrib COMMA attribs { $1::$3 }

attrib :
    | IDENT EQUAL attrib_value { ($1, $3) }

attrib_value: 
    | IDENT { $1 }
    | STRING { $1 }
    | NUM { string_of_int $1 }

%%

