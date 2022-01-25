# tree-sitter-tlaplus
[![Build & Test](https://github.com/tlaplus-community/tree-sitter-tlaplus/actions/workflows/ci.yml/badge.svg)](https://github.com/tlaplus-community/tree-sitter-tlaplus/actions/workflows/ci.yml)
[![npm](https://img.shields.io/npm/v/@tlaplus/tree-sitter-tlaplus.svg)](https://www.npmjs.com/package/@tlaplus/tree-sitter-tlaplus)
[![crates.io](https://img.shields.io/crates/v/tree-sitter-tlaplus.svg)](https://crates.io/crates/tree-sitter-tlaplus)

## Overview
This is a [tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar for the formal specification language [TLA+](https://en.wikipedia.org/wiki/TLA%2B) (and [PlusCal](https://en.wikipedia.org/wiki/PlusCal)).
Tree-sitter is an incremental error-tolerant parser generator primarily aimed at language tooling such as highlighting, code folding, symbol finding, and other tasks making use of its fully-featured syntax tree query API.
This grammar is intended to function gracefully while parsing a source file mid-edit, when the syntax isn't fully correct.
It is also fast enough to re-parse the file on every keystroke.
You can take the parser for a spin at https://tlaplus-community.github.io/tree-sitter-tlaplus/

The most important files in this repo are `grammar.js` and `src/scanner.cc`.
The former is the source of truth for parser code generation and the latter contains logic for parsing the context-sensitive parts of TLA+ like nested proofs and conjunction/disjunction lists.

## Aims & Capabilities
The aim of this project is to facilitate creation of modern user-assistive language tooling for TLA+.
To that end, the project provides two main capabilities:
1. Provide an approximately-correct parse tree for TLA+ specifications in standardized form, for easy integration with general projects designed to consume the tree-sitter grammars of many languages.
1. Provide a [tree query API](https://tree-sitter.github.io/tree-sitter/using-parsers#pattern-matching-with-queries) for efficiently querying the TLA+ parse tree, in addition to an API for arbitrary programmatic exploration of same, with bindings in multiple languages for easy integration with projects specifically targeting TLA+.

The correctness criterion of this parser is as follows: if the TLA+ specification being parsed constitutes valid TLA+ (both syntactically and semantically), the parse tree will be correct.
If the spec is not valid TLA+, the parse tree will be approximately correct - perhaps permissively allowing illegal syntax, or interpreting erroneous syntax in strange ways.
This permissive behavior makes it excellent for user-assistive language tooling, but probably a poor choice as the backbone for an interpreter or model-checker.
Application possibilities include:
 * Advanced syntax highlighting
 * Syntax-aware code folding
 * Lightweight backend for a TLA+ [language server](https://microsoft.github.io/language-server-protocol/)
 * Writing TLA+ specs via dictation using [Cursorless](https://github.com/pokey/cursorless-vscode)
 * Semantic analysis of TLA+ specs [on GitHub](https://github.com/github/semantic)
 * Real-time translation of TLA+ operator symbols into their unicode equivalents

If you really want to use this project to write an interpreter, nobody's stopping you from trying.
You could first use SANY to check spec validity, then use this parser to extract & interact with the actual parse tree.
For a REPL, you might want to wait until the [multiple entry points](https://github.com/tree-sitter/tree-sitter/issues/870) feature is added to tree-sitter so you can parse standalone TLA+ expressions without an encapsulating module.

## Use & Notable Integrations
There are a number of avenues available for consuming & using the parser in a project of your own; see the [tlaplus-tool-dev-examples](https://github.com/tlaplus-community/tlaplus-tool-dev-examples) repo.

Notable projects currently using or integrating this grammar include:
 * [nvim-treesitter](https://github.com/nvim-treesitter/nvim-treesitter) for TLA+ syntax highlighting & code folding in Neovim
 * [tla-mode](https://github.com/carlthuringer/tla-mode) for TLA+ syntax highlighting in Emacs

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

## The Playground
The playground enables you to easily try out the parser in your browser.
You can use the playground [online](https://tlaplus-community.github.io/tree-sitter-tlaplus/) (serving the latest parser version from the main branch) or set it up locally as follows:
1. Install Emscripten 2.0.17 or **earlier** ([why?](https://github.com/tree-sitter/tree-sitter/issues/1098#issuecomment-842326203))
1. Run `tree-sitter build-wasm`
1. Run `tree-sitter playground`

The playground consists of a pane containing an editable TLA+ spec, and another pane containing the parse tree for that spec.
The parse tree is updated in real time as you edit the TLA+ spec.
You can click parse tree nodes to highlight the corresponding snippet of TLA+, and move the cursor around the spec to show the corresponding parse tree node.
You can click the "log" checkbox and open your browser's development console to see the parser's debug output as it attempts to parse the TLA+ spec.
You can also click the "query" checkbox to open a third pane for testing [tree queries](https://tree-sitter.github.io/tree-sitter/using-parsers#pattern-matching-with-queries); for example, enter the following to match all operator names in a capture named `@operator` (indicated by the names becoming highlighted):
```
(operator_definition name: (identifier) @operator)
```

## Contributions
Pull requests are welcome. If you modify `grammar.js`, make sure you run `tree-sitter generate` before committing & pushing.
Generated files are (unfortunately) currently present in the repo but will hopefully be removed in [the future](https://github.com/tree-sitter/tree-sitter/discussions/1243).
Their correspondence is enforced during CI.
