# tree-sitter-tlaplus
This is a [tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar for [TLA+](https://en.wikipedia.org/wiki/TLA%2B), a formal specification language.
Tree-sitter is an incremental error-tolerant parser generator primarily aimed at language tooling such as highlighting, code folding, symbol finding, and other tasks requiring knowledge of the syntax tree.
This grammar is intended to function gracefully when parsing a source file mid-edit, when the full syntax isn't correct.
It is also fast enough to re-parse the file on every keystroke.
You can take the parser for a spin at https://tlaplus-community.github.io/tree-sitter-tlaplus/

## Build & Test
1. Install [Node.js and npm](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm)
1. Install a C compiler
1. Clone the repo
1. Open a terminal in the repo root and run `npm install` to build
1. Run `tree-sitter test` to run the tests
