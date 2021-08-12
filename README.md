# tree-sitter-tlaplus
[![Build & Test](https://github.com/tlaplus-community/tree-sitter-tlaplus/actions/workflows/ci.yml/badge.svg)](https://github.com/tlaplus-community/tree-sitter-tlaplus/actions/workflows/ci.yml)

## Overview
This is a [tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar for [TLA+](https://en.wikipedia.org/wiki/TLA%2B), the formal specification language.
Tree-sitter is an incremental error-tolerant parser generator primarily aimed at language tooling such as highlighting, code folding, symbol finding, and other tasks making use of its fully-featured syntax tree query API.
This grammar is intended to function gracefully while parsing a source file mid-edit, when the syntax isn't fully correct.
It is also fast enough to re-parse the file on every keystroke.
You can take the parser for a spin at https://tlaplus-community.github.io/tree-sitter-tlaplus/

## Use
There are a number of avenues available for consuming & using the parser:
 * Use this grammar's [node module](https://www.npmjs.com/package/@tlaplus/tree-sitter-tlaplus) in conjunction with the tree-sitter [node.js bindings](https://www.npmjs.com/package/tree-sitter); see the [typescript example](examples/typescript).
 * Use this grammar's [rust crate](https://crates.io/crates/tree-sitter-tlaplus) in conjunction with the tree-sitter [rust bindings](https://crates.io/crates/tree-sitter); see the [rust example](examples/rust).
 * Use the [tree-sitter CLI](https://github.com/tree-sitter/tree-sitter/blob/master/cli/README.md) to directly parse or highlight files from the command line (this is mostly used for development & testing).

## Build & Test
1. Install [Node.js and npm](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm)
1. Install a C compiler
1. Clone the repo with the `--recurse-submodules` parameter
1. Open a terminal in the repo root and run `npm install` to download packages & build the project
1. Ensure `node_modules/.bin` is on your path
1. Run `tree-sitter test` to run the unit tests
1. Run corpus tests (parsing all specifications in the [tlaplus/examples](https://github.com/tlaplus/examples) repo) with the following powershell commands (no output if successful):
   - `$specs = Get-ChildItem -Path .\test\examples\external\specifications -Filter "*.tla" -Exclude "Reals.tla","Naturals.tla" -Recurse`
   - `$specs |% {tree-sitter parse -q $_}`

## Run Playground
You can use the playground [online](https://tlaplus-community.github.io/tree-sitter-tlaplus/) or set it up locally as follows:
1. Install Emscripten 2.0.17 or **earlier** ([why?](https://github.com/tree-sitter/tree-sitter/issues/1098#issuecomment-842326203))
1. Run `tree-sitter build-wasm`
1. Run `tree-sitter playground`

## Contributions
Pull requests are welcome. If you modify the `grammar.js`, make sure you run `tree-sitter generate` before committing & pushing.
Generated files are (unfortunately) currently present in the repo but will hopefully be removed in [the future](https://github.com/tree-sitter/tree-sitter/discussions/1243).
Their correspondence is enforced during CI.
