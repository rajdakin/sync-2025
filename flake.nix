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

            src = ./theories;
            version = "0.1.0";

            useDune = true;
          };

          extracted = ocamlPackages.buildDunePackage {
            pname = "extracted";

            src = ./extracted;
            version = "0.1.0";

            nativeBuildInputs = [ coqPackages.coq ];
            buildInputs = [ packages.theories ];
          };

          compiler = ocamlPackages.buildDunePackage {
            pname = "compiler";

            src = ./compiler;
            version = "0.1.0";

            nativeBuildInputs = [ ocamlPackages.menhir ];
            buildInputs = [ packages.extracted ];
          };

          default = packages.compiler;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = with packages; [ compiler extracted theories ];
          packages =
            (with coqPackages; [ vscoq-language-server ])
            ++ (with ocamlPackages; [
              ocamlformat
              merlin
              ocaml-lsp
            ]);
        };

        formatter = pkgs.nixfmt-rfc-style;
      }
    );
}
