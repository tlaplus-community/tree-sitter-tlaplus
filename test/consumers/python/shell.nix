{ pkgs ? import <nixpkgs> { } }:

let pythonEnv = pkgs.python3.withPackages(ps: [ ]);
in pkgs.mkShell {
  packages = [
    pythonEnv
  ];
}

