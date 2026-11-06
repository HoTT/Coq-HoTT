{
  description = "A Rocq library for Homotopy Type Theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";

    flake-utils.url = "github:numtide/flake-utils";

    dune = {
      url = "github:ocaml/dune";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, dune }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        makeDevShell = { rocq, extraPackages ? [ ] }:
          let
            ocamlPackages = rocq.ocamlPackages;
          in
          pkgs.mkShell {
            buildInputs = [
              dune.packages.${system}.default
              ocamlPackages.ocaml
              ocamlPackages.findlib
              pkgs.pkg-config
              (pkgs.python3.withPackages (ps: [
                ps.pygments
                ps.dominate
                ps.beautifulsoup4
                ps.docutils
              ]))
              rocq
            ] ++ extraPackages;
          };
      in
      {
        packages.default = pkgs.rocqPackages.mkRocqDerivation {
          pname = "hott";
          version = "9.0";
          opam-name = "coq-hott";
          src = self;
          useDune = true;
        };

        devShells = rec {
          default = rocq_9_1;

          rocq_9_3 = makeDevShell {
            rocq = pkgs.rocqPackages_9_3.rocq-core;
          };

          rocq_9_2 = makeDevShell {
            rocq = pkgs.rocqPackages_9_2.rocq-core;
          };

          rocq_9_1 = makeDevShell {
            rocq = pkgs.rocqPackages_9_1.rocq-core;
            # coq-lsp retains its upstream package name.
            extraPackages = [ pkgs.rocqPackages_9_1.coq-lsp ];
          };

          # To use, pass --impure to nix develop.
          rocq_master = makeDevShell {
            rocq = pkgs.rocqPackages.rocq-core.override { version = "master"; };
          };
        };

        formatter = pkgs.nixpkgs-fmt;
      });
}
