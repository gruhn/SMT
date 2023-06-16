{ pkgs ? import <nixpkgs> {} }:

let
  inherit (pkgs) haskellPackages;
in

pkgs.mkShell {
  buildInputs = with haskellPackages; [
    ghc
    cabal-install
    haskell-language-server
  ];

  # shellHook = ''
  #   export PATH="$PATH:${haskellPackages.ghc}/bin:${haskellPackages.cabal-install}/bin:${haskellPackages.haskell-language-server}/bin"
  # '';
}
