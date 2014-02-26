(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*            This file is part of the DpdGraph tools.                        *)
(*   Copyright (C) 2009-2013 Anne Pacalet (Anne.Pacalet@free.fr)           *)
(*             ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~                                *)
(*        This file is distributed under the terms of the                     *)
(*         GNU Lesser General Public License Version 2.1                      *)
(*        (see the enclosed LICENSE file for mode details)                    *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let version_option = ref false

let out_file = ref None
let set_out_file file = out_file := Some file

let graphname = ref None
let set_graphname name = graphname := Some name

let spec_args = [
  ("-o", Arg.String set_out_file,
      ": name of output file (default: name of input file .dot)");
  ("-with-defs", Arg.Set Dpd_compute.with_defs,
      ": show everything (default)");
  ("-without-defs", Arg.Clear Dpd_compute.with_defs,
      ": show only Prop objects");
  ("-rm-trans", Arg.Set Dpd_compute.reduce_trans,
      ": remove transitive dependencies (default)");
  ("-keep-trans", Arg.Clear Dpd_compute.reduce_trans,
      ": keep transitive dependencies");
  ("-graphname", Arg.String set_graphname,
      ": name of graph (default: name of input file)");
  ("-debug", Arg.Set Dpd_compute.debug_flag,
      ": set debug mode");
  ("-v", Arg.Set version_option,
      ": print version and exit");
]

let do_file n f =
  try
    Dpd_compute.feedback "read file %s@." f;
    let g = Dpd_lex.read f in
    let g = Dpd_compute.build_graph g in
      Dpd_compute.simplify_graph g;
    let dotfile = match !out_file with
      | None -> (Filename.chop_extension f)^".dot"
      | Some f ->
          if n = 0 then f
          else (Filename.chop_extension f)^"."^(string_of_int n)^".dot" in
    let graph_name = match !graphname with
      | None -> (Filename.chop_extension f)
      | Some name -> name
    in
      Dpd_dot.graph_file graph_name dotfile g
  with Dpd_compute.Error msg -> Dpd_compute.error "%s@." msg

let main () =
  let usage_msg = "Usage : "^(Sys.argv.(0))^" [options]" in
  let args = ref [] in
  let memo_arg arg = args := arg :: !args in
    Arg.parse spec_args memo_arg usage_msg;
    if !version_option
    then Format.printf "This is '%s' (part of DpdGraph tools - version %s)@."
           (Filename.basename Sys.argv.(0)) Version.version
    else match !args with
      |  [] -> Dpd_compute.error "no source file to process ?@.";
               Arg.usage spec_args usage_msg
      | f::[]  -> do_file 0 f
      | l  ->
          ignore (List.fold_left (fun n f -> do_file n f; n+1) 1 l)

let () = main ()
