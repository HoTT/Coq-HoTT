{
  description = "A Coq library for Homotopy Type Theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";

    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        makeDevShell = { coq ? pkgs.coq }:
          let
            coqPackages = pkgs.mkCoqPackages coq // {
              __attrsFailEvaluation = true;
            };
          in
          { extraPackages ? [ coqPackages.coq-lsp ] }:
          pkgs.mkShell {
            buildInputs =
              [ pkgs.dune_3 pkgs.ocaml ] ++ extraPackages ++ [ coq ];
          };
      in
      {
        packages.default = pkgs.coqPackages.mkCoqDerivation {
          pname = "hott";
          version = "8.20";
          src = self;
          useDune = true;
        };

        devShells.default =
          makeDevShell
            { coq = pkgs.coq_8_20; }
            { };

        devShells.coq_8_19 =
          makeDevShell
            { coq = pkgs.coq_8_19; }
            { };

        # To use, pass --impure to nix develop
        devShells.coq_master =
          makeDevShell
            { coq = pkgs.coq.override { version = "master"; }; }
            { extraPackages = [ ]; };

        formatter = pkgs.nixpkgs-fmt;
      });
}
