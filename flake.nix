{
  description = "A Coq library for Homotopy Type Theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    ,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        coq_version = pkgs.coq_8_17;
      in
      {
        packages.default = pkgs.coqPackages.mkCoqDerivation {
          pname = "hott";
          version = "8.17";
          src = self;
          useDune = true;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            dune_3
            ocaml
            coq_8_17
            coqPackages_8_17.coq-lsp
          ];
        };

        formatter = pkgs.nixpkgs-fmt;
      }
    );
}
