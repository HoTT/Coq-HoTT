{
  description = "A Coq library for Homotopy Type Theory";

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
        makeDevShell = { coq ? pkgs.coq, rocqPackages ? coq.passthru.rocqPackages or null }:
          let
            coqPackages = pkgs.mkCoqPackages coq // {
              __attrsFailEvaluation = true;
            };
            ocamlPackages = coq.passthru.ocamlPackages or pkgs.ocamlPackages;
          in
          { extraPackages ? [ coqPackages.coq-lsp ] }:
          pkgs.mkShell {
            buildInputs =
              [
                dune.packages.${system}.default
                ocamlPackages.ocaml
                ocamlPackages.findlib
                pkgs.pkg-config
              ] ++ extraPackages ++ [ coq ]
              ++ pkgs.lib.optionals (rocqPackages != null) [ rocqPackages.rocq-core ];
          };
      in
      {
        packages.default = pkgs.coqPackages.mkCoqDerivation {
          pname = "hott";
          version = "9.0";
          src = self;
          useDune = true;
        };

        devShells.default =
          makeDevShell
            { coq = pkgs.coq_9_1; }
            { };

        devShells.coq_9_0 =
          makeDevShell
            { coq = pkgs.coq_9_0; }
            { };

        # To use, pass --impure to nix develop
        devShells.coq_master =
          makeDevShell
            { coq = pkgs.coq.override { version = "master"; }; }
            { extraPackages = [ ]; };

        formatter = pkgs.nixpkgs-fmt;
      });
}
