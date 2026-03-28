(* Generate dune rules for parallel alectryon processing using fcc *)
(* Rules are included from alectryon-html subdir, so paths use ../ prefix *)

let find_v_files dirs =
  let files = ref [] in
  let rec walk dir =
    let entries = Sys.readdir dir in
    Array.iter (fun entry ->
      let path = Filename.concat dir entry in
      if Sys.is_directory path then
        walk path
      else if Filename.check_suffix entry ".v" then
        files := path :: !files
    ) entries
  in
  List.iter (fun dir -> if Sys.file_exists dir then walk dir) dirs;
  List.sort String.compare !files

let v_to_module path =
  (* theories/Foo/Bar.v -> HoTT.Foo.Bar
     contrib/Foo.v -> HoTT.Contrib.Foo *)
  let base = Filename.chop_suffix path ".v" in
  let parts = String.split_on_char '/' base in
  match parts with
  | "theories" :: rest -> "HoTT." ^ String.concat "." rest
  | "contrib" :: rest -> "HoTT.Contrib." ^ String.concat "." rest
  | _ -> String.concat "." parts

let v_to_html path =
  Printf.sprintf "%s.html" (v_to_module path)

let print_rule vfile =
  let html_target = v_to_html vfile in
  let alectryon_json = vfile ^ ".alectryon.json" in
  Printf.printf "\n(rule\n";
  Printf.printf " (target %s)\n" html_target;
  Printf.printf " (deps\n";
  Printf.printf "  (sandbox always)\n";
  Printf.printf "  ../%s\n" vfile;
  Printf.printf "  ../_CoqProject\n";
  Printf.printf "  (glob_files_rec ../theories/*.vo)\n";
  Printf.printf "  (glob_files_rec ../contrib/*.vo)\n";
  Printf.printf "  ../etc/gen-alectryon-rules/goaldump-to-alectryon.py\n";
  Printf.printf "  (source_tree ../etc/alectryon))\n";
  let log_target = v_to_module vfile ^ ".v.fcc.log" in
  Printf.printf " (action\n";
  Printf.printf "  (chdir ..\n";
  Printf.printf "   (progn\n";
  Printf.printf "    (with-outputs-to alectryon-html/%s (with-accepted-exit-codes (or 0 1) (run fcc --root=. --no_vo --plugin=coq-lsp.plugin.goaldump %s)))\n" log_target vfile;
  Printf.printf "    (run python3 etc/gen-alectryon-rules/goaldump-to-alectryon.py %s -o %s)\n" vfile alectryon_json;
  Printf.printf "    (run python3 etc/alectryon/alectryon.py --frontend coq.io.json %s --backend webpage -o alectryon-html/%s)))))\n" alectryon_json html_target

let () =
  let dirs = ["theories"; "contrib"] in
  let files = find_v_files dirs in

  (* Print individual rules *)
  List.iter print_rule files;

  (* Print umbrella alias *)
  Printf.printf "\n(alias\n (name alectryon)\n (deps\n";
  List.iter (fun vfile -> Printf.printf "  %s\n" (v_to_html vfile)) files;
  Printf.printf "))\n"
