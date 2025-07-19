{ pkgs ? import <nixpkgs> {} }:

# note: cabal can cache the location of ghc
# if this happens (ex: can't find file and is looking for wrong ghc version in store)
# remove all files related to cabal and run nix-shell again

pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [
    cabal-install
    z3
    cvc5
    ghc
    git
  ];
  shellHook = ''
    bash base_setup.sh
    cabal update
  '';
}
