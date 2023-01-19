#! /bin/sh

find "test/examples/external/specifications" -name "*.tla" |
    xargs -P $(nproc) -I {} "./node_modules/.bin/tree-sitter parse -q {}"

