(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*            This file is part of the DpdGraph tools.                        *)
(*   Copyright (C) 2009-2013 Anne Pacalet (Anne.Pacalet@free.fr)           *)
(*             ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~                                *)
(*        This file is distributed under the terms of the                     *)
(*         GNU Lesser General Public License Version 2.1                      *)
(*        (see the enclosed LICENSE file for mode details)                    *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


module C = Dpd_compute
module G = Dpd_compute.G
module Node = Dpd_compute.Node

let color_soft_yellow = (0xFFFFC3)

let color_pale_orange = (0xFFE1C3) 
let color_medium_orange = (0xFFB57F)

let color_soft_green = (0x7FFFD4)
let color_medium_green = (0x00E598)

let color_soft_pink = (0xFACDEF)
let color_medium_pink = (0xF070D1)

let color_soft_purple = (0xE2CDFA)
let color_soft_blue = (0x7FAAFF)

type attr_kind = 
  | Aid of string
  | Astr of string
  | Acolor of int
  | Aint of int
  | Aurl of string

let split_string s i =
  let s1 = String.sub s 0 i in
  let s2 = String.sub s (i+1) ((String.length s) - (i+1)) in
    s1, s2

let mk_url n = 
  let df, dm = match Node.get_attrib "path" n with
    | None -> "", ""
    | Some d -> 
        try let i = String.index d '.' in
        let df, dm = split_string d i in
          df, dm^"."
        with Not_found -> d, ""
  in
  df^".html"^"#"^dm^(Node.name n)

let node_attribs g n =
  let attr = [] in
  let color = match Node.get_attrib "kind" n with
    | Some s when s = "cnst" ->
        begin 
          let is_prop = 
            match Node.bool_attrib "prop" n with 
              | Some b -> b | None -> false
          in
            match Node.bool_attrib "body" n with
              | Some true ->
                  (if is_prop then color_soft_green else color_medium_pink)
              | _ -> (if is_prop then color_medium_orange else color_soft_pink)
        end
    | Some s when s = "inductive"-> color_soft_purple
    | Some s when s = "construct" -> color_soft_blue
    | _ -> (0x000000) (* TODO warning *)
  in
  let attr = (Aid "fillcolor", Acolor color) :: attr in
  let used = List.length (G.pred g n) > 0 in
  let attr = if used then attr else (Aid "peripheries", Aint 3) :: attr in
  let label = String.escaped (Node.name n) in
  let url = mk_url n in
  let attr = (Aid "URL", Aurl url)::attr in
  let attr = (Aid "label", Astr label)::attr in
    attr

let add_node_in_subgraph sg_tbl n sg =
  let rec get_subgraph sg =
    try Hashtbl.find sg_tbl sg 
    with Not_found -> (* new subgraph *)
      C.debug "New subgraph : %s@." sg;
      try 
        let i = String.rindex sg '.' in
        let d, n = split_string sg i in
        let (level, ssg, nodes) = get_subgraph d in
          C.debug "add subgraph %s in %s@." n d;
          Hashtbl.replace sg_tbl d (level, (sg,n)::ssg, nodes);
          (level+1, [], [])
      with Not_found -> (* simple subgraph *) 0, [], []
  in
  let (l, ssg, nodes) = get_subgraph sg in
    Hashtbl.replace sg_tbl sg (l, ssg, n::nodes)

let str2id s = 
  let char = function  '.' | '\'' -> '_' |  c -> c in
    for i = 0 to String.length s - 1 do s.[i] <- char s.[i] done; s 

let rec print_attribs sep fmt attribs = 
  let print_a fmt a = match a with
    | Aid s -> Format.fprintf fmt "%s" s
    | Astr s -> Format.fprintf fmt "\"%s\"" s
    | Aurl s -> Format.fprintf fmt "<%s>" s
    | Acolor color -> Format.fprintf fmt "\"#%06X\"" color
    | Aint i -> Format.fprintf fmt "%d" i
  in
  let print_attrib fmt (a, b) = 
    Format.fprintf fmt "%a=%a" print_a a print_a b 
  in
    match attribs with [] -> ()
      | a::[] -> Format.fprintf fmt "%a" print_attrib a
      | a::tl -> Format.fprintf fmt "%a%s%a" 
                   print_attrib a sep (print_attribs sep) tl

let node_dot_id n = (* was Node.id n *)
  let dirname = match Node.get_attrib "path" n with
    | None -> ""
    | Some d -> d
  in str2id (dirname^"_"^(Node.name n))

(* the subgraph table map sg full name to (sglevel, sg_subgraphs, sg_nodes)
 * The level is 0 for toplevel subgraphs.
 * sg_subgraphs is a list of (sg_full_name, sg_short_name).
 * sg_nodes is the list of nodes in the subgraph.
 * *)
let print_subgraphs fmt sg_tbl =
  let rec print_subgraph sg_path sg_name (sglev, ssg, nodes) =
    let sg_id = "cluster_"^(str2id sg_path) in
    let sg_attribs =
      (Aid "label", Astr sg_name)::
      (Aid "fillcolor", Acolor (color_soft_yellow - 32*sglev))::
      (Aid "labeljust", Aid "l")::
      (Aid "style", Aid "filled")::
      []
    in
      Format.fprintf fmt "subgraph %s { %a @." sg_id
        (print_attribs "; ") sg_attribs;
      List.iter print_sub_subgraph ssg;
      List.iter (fun n -> Format.fprintf fmt "%s; " (node_dot_id n)) nodes;
      Format.fprintf fmt "};@."
  and print_sub_subgraph (sg_id, sg_name) =
    try 
      let ssg = Hashtbl.find sg_tbl sg_id in print_subgraph sg_id sg_name ssg
    with Not_found -> assert false
  in
  let print_top_subgraph sg ((l,_,_) as info)  =
    if l = 0 then print_subgraph sg sg info
  in
    Hashtbl.iter print_top_subgraph sg_tbl

(** don't use Graph.Graphviz because of attribute limitations (URL, subgraph,
* ...) *)
let print_graph fmt graph = 
  let subgraphs = Hashtbl.create 7 in
  let print_node n =
     let attribs = node_attribs graph n in
       Format.fprintf fmt "%s [%a] ;@." 
         (node_dot_id n) (print_attribs ", ") attribs;
     let _ = match Node.get_attrib "path" n with None | Some "" -> ()
       | Some d -> add_node_in_subgraph subgraphs n d
    in ()
  in
  let print_edge e = 
    let edge_attribs = [] in
    (* let edge_attribs = (Aid "style", Aid "bold")::edge_attribs in *)
    Format.fprintf fmt "  %s -> %s [%a] ;@."
      (node_dot_id (G.E.src e)) (node_dot_id (G.E.dst e))
      (print_attribs ", ") edge_attribs
  in
  Format.fprintf fmt "digraph G {@.";
  Format.fprintf fmt "  graph [ratio=0.5]@.";
  Format.fprintf fmt "  node [style=filled]@.";
  G.iter_vertex print_node graph;
  G.iter_edges_e print_edge graph;
  print_subgraphs fmt subgraphs;
  Format.fprintf fmt "} /* END */@."


let graph_file filename g =
  let file, oc = 
    try filename, open_out filename
    with Sys_error msg ->
      C.warning "cannot open file: %s@." msg;
      let file = Filename.temp_file "coqdpd" ".dpd" in
        file, open_out file
  in C.feedback "Graph output in %s@." file;
     let fmt = Format.formatter_of_out_channel oc in
       print_graph fmt g;
       close_out oc

