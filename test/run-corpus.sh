#! /bin/sh

find "test/examples/external/specifications" -name "*.tla" ! -iname "Reals.tla" ! -iname "Naturals.tla" |
    xargs -P $(nproc) -I {} npx tree-sitter parse -q {}
