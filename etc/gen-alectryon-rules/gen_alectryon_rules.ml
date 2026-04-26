(* Generate dune rules for parallel alectryon processing using fcc.
   Rules are included from the alectryon-html subdir via dynamic_include,
   so dependency paths need ../ prefixing — handled by the dep printer.
   Actions use (chdir ..) to run from the project root. *)

(* -- Data types --------------------------------------------------------- *)

(* Dependencies. [`File] paths are relative to the project root;
   the printer adds the ../ prefix. [`Local] paths are relative to
   alectryon-html/ and are emitted as-is. *)
type dep =
  [ `File of string
  | `Glob_rec of string
  | `Source_tree of string
  | `Alias of string
  | `Local of string
  | `Sandbox ]

(* Actions. [`Atom] is a pre-formatted sexp string for leaf actions. *)
type action =
  [ `Atom of string
  | `In_project of action
  | `Progn of action list
  | `Outputs_to of string * action
  | `Stdout_to of string * action ]

type stanza =
  [ `Rule of string list * dep list * action
  | `Alias_stanza of string * string list ]

(* -- Sexp printer ------------------------------------------------------- *)

let open_sexp fmt name = Format.fprintf fmt "@ @[<v 1>(%s" name
let close fmt = Format.fprintf fmt ")@]"
let item fmt s = Format.fprintf fmt "@ %s" s

let pp_dep fmt = function
  | `File path -> item fmt ("../" ^ path)
  | `Glob_rec pattern -> item fmt (Printf.sprintf "(glob_files_rec ../%s)" pattern)
  | `Source_tree dir -> item fmt (Printf.sprintf "(source_tree ../%s)" dir)
  | `Alias path -> item fmt (Printf.sprintf "(alias ../%s)" path)
  | `Local path -> item fmt path
  | `Sandbox -> item fmt "(sandbox always)"

let rec pp_action fmt = function
  | `Atom s -> item fmt s
  | `In_project a ->
    open_sexp fmt "chdir .."; pp_action fmt a; close fmt
  | `Progn actions ->
    open_sexp fmt "progn"; List.iter (pp_action fmt) actions; close fmt
  | `Outputs_to (file, a) ->
    open_sexp fmt (Printf.sprintf "with-outputs-to %s" file);
    pp_action fmt a; close fmt
  | `Stdout_to (file, a) ->
    open_sexp fmt (Printf.sprintf "with-stdout-to %s" file);
    pp_action fmt a; close fmt

let pp_stanza fmt = function
  | `Rule (targets, deps, action) ->
    open_sexp fmt "rule";
    (match targets with
     | [t] -> item fmt (Printf.sprintf "(target %s)" t)
     | ts -> item fmt (Printf.sprintf "(targets %s)" (String.concat " " ts)));
    open_sexp fmt "deps";
    List.iter (pp_dep fmt) deps;
    close fmt;
    open_sexp fmt "action"; pp_action fmt action; close fmt;
    close fmt
  | `Alias_stanza (name, deps) ->
    open_sexp fmt "alias";
    item fmt (Printf.sprintf "(name %s)" name);
    open_sexp fmt "deps";
    List.iter (item fmt) deps;
    close fmt;
    close fmt

(* -- File discovery and naming ------------------------------------------ *)

let find_v_files dirs =
  let files = ref [] in
  let rec walk dir =
    let entries = Sys.readdir dir in
    Array.iter (fun entry ->
      let path = Filename.concat dir entry in
      if Sys.is_directory path then walk path
      else if Filename.check_suffix entry ".v" then
        files := path :: !files
    ) entries
  in
  List.iter (fun dir -> if Sys.file_exists dir then walk dir) dirs;
  List.sort String.compare !files

let v_to_module path =
  let base = Filename.chop_suffix path ".v" in
  let parts = String.split_on_char '/' base in
  match parts with
  | "theories" :: rest -> "HoTT." ^ String.concat "." rest
  | "contrib" :: rest -> "HoTT.Contrib." ^ String.concat "." rest
  | _ ->
    Printf.eprintf "Warning: unexpected path %s (expected theories/ or contrib/)\n" path;
    String.concat "." parts

(* -- Rule construction -------------------------------------------------- *)

let extraction_rule vfile : stanza =
  let m = v_to_module vfile in
  `Rule (
    [m ^ ".v.alectryon.json"; m ^ ".v.fcc.log"],
    [ `Sandbox
    ; `File vfile
    ; `File "_CoqProject"
    ; `Glob_rec "theories/*.vo"
    ; `Glob_rec "contrib/*.vo"
    ; `File "etc/gen-alectryon-rules/goaldump-to-alectryon.py" ],
    `In_project (`Progn [
      `Outputs_to (Printf.sprintf "alectryon-html/%s.v.fcc.log" m,
        `Atom (Printf.sprintf "(run fcc --root=%%{project_root} --no_vo \
          --plugin=coq-lsp.plugin.goaldump %%{project_root}/%s)" vfile));
      `Atom (Printf.sprintf "(run python3 \
        etc/gen-alectryon-rules/goaldump-to-alectryon.py \
        %s -o alectryon-html/%s.v.alectryon.json)" vfile m);
    ]))

let rendering_rule vfile : stanza =
  let m = v_to_module vfile in
  `Rule (
    [m ^ ".html"],
    [ `Local (m ^ ".v.alectryon.json")
    ; `File "etc/alectryon/alectryon.py"
    ; `Source_tree "etc/alectryon/alectryon" ],
    `In_project (`Atom (Printf.sprintf
      "(run python3 etc/alectryon/alectryon.py \
       --frontend coq.io.json alectryon-html/%s.v.alectryon.json \
       --backend webpage --copy-assets none \
       -o alectryon-html/%s.html)" m m)))

let copy_asset src target : stanza =
  `Rule ([target], [`File src],
    `Atom (Printf.sprintf "(copy ../%s %%{target})" src))

let coqdoc_asset name : stanza =
  `Rule ([name], [`Alias "theories/doc"],
    `Atom (Printf.sprintf "(copy ../theories/HoTT.html/%s %%{target})" name))

let pygments_rule : stanza =
  `Rule (["pygments.css"], [],
    `Stdout_to ("%{target}",
      `Atom (Printf.sprintf "(run python3 -c %S)"
        "from pygments.formatters import HtmlFormatter; \
         print(HtmlFormatter(style='colorful').get_style_defs('.highlight'))")))

(* -- Main --------------------------------------------------------------- *)

let () =
  let fmt = Format.std_formatter in
  let files = find_v_files ["theories"; "contrib"] in

  let per_file_rules =
    List.concat_map (fun vfile ->
      [extraction_rule vfile; rendering_rule vfile]
    ) files
  in
  let asset_rules =
    [ copy_asset "etc/alectryon/alectryon/assets/alectryon.css" "alectryon.css"
    ; copy_asset "etc/alectryon/alectryon/assets/alectryon.js" "alectryon.js"
    ; pygments_rule
    ; coqdoc_asset "index.html"
    ; coqdoc_asset "toc.html"
    ; coqdoc_asset "coqdoc.css" ]
  in
  let umbrella =
    `Alias_stanza ("alectryon",
      ["alectryon.css"; "alectryon.js"; "pygments.css";
       "index.html"; "toc.html"; "coqdoc.css"]
      @ List.map (fun vfile -> v_to_module vfile ^ ".html") files)
  in

  let all_stanzas = per_file_rules @ asset_rules @ [umbrella] in
  Format.fprintf fmt "@[<v 0>";
  List.iter (pp_stanza fmt) all_stanzas;
  Format.fprintf fmt "@]@."
