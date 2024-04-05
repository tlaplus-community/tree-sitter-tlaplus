let pkgs = import <nixpkgs> {};
in pkgs.mkShell {
  packages = with pkgs; [
    (pkgs.python3.withPackages (python-pkgs: [
      python-pkgs.setuptools
      python-pkgs.wheel
      python-pkgs.build
    ]))
    (tree-sitter.override { webUISupport = true; })
    emscripten
    gcc
  ];
}

