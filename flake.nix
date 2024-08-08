{
  description = "";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = nixpkgs.legacyPackages.${system}; 
      in 
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            haskell.compiler.ghc96
            haskell.packages.ghc96.haskell-language-server
            haskell.packages.ghc96.cabal-install
            haskell.packages.ghc96.implicit-hie
          ];
        };
      }
    );
}
