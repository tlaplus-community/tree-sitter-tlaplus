{ pkgs ? import <nixpkgs> {} }:

let
  unstable = import (fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/nixpkgs-unstable.tar.gz";
    sha256 = "0lisfh5b3dgcjb083nsxmffvzxzs6ir1jfsxfaf29gjpjnv7sm7f";
  }) {};
in

pkgs.mkShell {
  packages = [
    (pkgs.python3.withPackages (python-pkgs: [
      python-pkgs.setuptools
      python-pkgs.wheel
      python-pkgs.build
    ]))
    (unstable.tree-sitter.override { webUISupport = true; })
    pkgs.emscripten
    pkgs.gcc
  ];
}

