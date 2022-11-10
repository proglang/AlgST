{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";

    flake-utils.url = "github:numtide/flake-utils";
    flake-utils.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        inherit (pkgs.writers) writeBashBin;

        pkgs = nixpkgs.legacyPackages.${system};

        accept-test = writeBashBin "accept-test" ''
          for f in "$@"; do
            mv "$f.actual" "$f.expected" && git add -- "$f" "$f.expected"
          done
        '';

        run-tests = writeBashBin "tests" ''
          echo -en '\033[1m'
          echo stack build --fast --test "$@"
          echo -en '\033[m'
          exec stack build --fast --test "$@"
        '';
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [ nixfmt accept-test run-tests ];
        };
      });
}
