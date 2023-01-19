#! /bin/sh

find "test/examples" -name "*.tla" |
    xargs -P $(nproc) -I {} ./node_modules/.bin/tree-sitter parse -q {}

