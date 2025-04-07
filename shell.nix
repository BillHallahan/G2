{ pkgs ? import <nixpkgs> {} }:

# note: cabal can cache the location of ghc for some reason :/
# if this happens (ex: can't find file and is looking for wrong ghc version in store)
# remove all related files and compile again

pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [ 
    cabal-install
    z3
    ghc
    git
  ];
  shellHook = ''
    bash base_setup.sh
    cabal update
  '';
}
