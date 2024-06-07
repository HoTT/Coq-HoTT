{
  description = "A Coq library for Homotopy Type Theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        makeDevShell = coqVersion:
          pkgs.mkShell {
            buildInputs = with pkgs."coqPackages_${coqVersion}"; [
              pkgs.dune_3
              pkgs.ocaml
              coq
              coq-lsp
            ];
          };
      in {
        packages.default = pkgs.coqPackages.mkCoqDerivation {
          pname = "hott";
          version = "8.18";
          src = self;
          useDune = true;
        };

        devShells.default = makeDevShell "8_19";

        formatter = pkgs.nixpkgs-fmt;
      });
}
