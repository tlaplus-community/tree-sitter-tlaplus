#! /bin/sh

find test/examples/external/specifications -name "*.tla" ! -iname "Reals.tla" ! -iname "Naturals.tla" |
    xargs -I {} npx tree-sitter parse -q {}
