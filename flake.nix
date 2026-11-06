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
        # TODO: Use the packaged 9.2 LSP once nixpkgs provides the upstream port.
        rocqLsp92 =
          let
            rev = "f49d7b391c8dc6599a00d126d7bfedc9efbdc2e7";
            scope = pkgs.mkRocqPackages
              (pkgs.rocqPackages_9_2.rocq-core // { dontFilter = true; });
          in
          (scope.coq-lsp.override {
            version = {
              version = "dev";
              location = {
                owner = "rocq-community";
                repo = "rocq-lsp";
                inherit rev;
                hash = "sha256-VJLe7zNcvbUN0QsA/cKuhyr6kHKGWDf9Wp8uFhHQGvw=";
              };
            };
          }).overrideAttrs (old: {
            postPatch = (old.postPatch or "") + ''
              rm -rf vendor
            '';
            meta = (old.meta or { }) // {
              changelog = "https://github.com/rocq-community/rocq-lsp/blob/${rev}/CHANGES.md";
            };
          });
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
            extraPackages = [ rocqLsp92 ];
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
