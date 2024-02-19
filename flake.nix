{
  description = "A Coq library for Homotopy Type Theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        packages.default = pkgs.coqPackages.mkCoqDerivation {
          pname = "hott";
          version = "8.18";
          src = self;
          useDune = true;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs.coqPackages_8_19; [
            pkgs.dune_3
            pkgs.ocaml
            coq
            coq-lsp
          ];
        };

        formatter = pkgs.nixpkgs-fmt;
      }
    );
}
