{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        agdaDependencies = [
          pkgs.agdaPackages.agda-categories
          (pkgs.agdaPackages.standard-library.overrideAttrs (oldAttrs: {
            version = "2.3";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "v2.3";
              hash = "sha256-JOeoek6OfyIk9vwTj5QUJU6LnRzwfiG0e0ysW6zbhZ8=";
            };
          }))
        ];
        agda-html = pkgs.agdaPackages.mkDerivation {
          pname = "dinaturals";
          version = "0.1.0";
          src = builtins.path { path = ./.; name = "dinaturals"; };
          everythingFile = ./All.agda;
          buildInputs = agdaDependencies;

          installPhase = '''';

          buildPhase = ''
            runHook preBuild
            # Make sure this builds with --safe
            agda --html --html-dir=$out --highlight-occurrences --safe All.agda +RTS -M32G
            runHook postBuild
          '';

          preConfigure = ''export AGDA_EXEC=agda'';
          # LC_ALL = "en_US.UTF-8";
          nativeBuildInputs = [ pkgs.glibcLocales ];

          meta = {
            platforms = pkgs.lib.platforms.unix;
          };
        }; in {
        devShells.default = pkgs.mkShell { buildInputs = [
          (pkgs.agda.withPackages agdaDependencies)
        ]; };
        packages = {
          inherit agda-html;
          default = agda-html;
        };
      }
    );
}
