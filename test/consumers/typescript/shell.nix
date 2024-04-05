let pkgs = import <nixpkgs> {};
in pkgs.mkShell {
  packages = with pkgs; [
    nodejs
    nodePackages.npm
  ];
}

