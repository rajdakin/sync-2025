{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      flake-utils,
      nixpkgs,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        coqPackages = pkgs.coqPackages_8_20;
        ocamlPackages = coqPackages.coq.ocamlPackages;
      in
      rec {
        packages = {
          theories = coqPackages.mkCoqDerivation rec {
            pname = "Reactive";
            opam-name = "Reactive";
            version = "0.1.0";

            src = ./.;
            useDune = true;
          };

          default = packages.theories;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = with packages; [ theories ];
          packages =
                   (with coqPackages; [ vscoq-language-server ])
                   ++ (with ocamlPackages; [
                      ocamlformat menhir merlin ocaml-lsp
                   ]);
        };

        formatter = pkgs.nixfmt-rfc-style;
      }
    );
}
