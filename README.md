# tree-sitter-tlaplus

[![Build & Test](https://github.com/tlaplus-community/tree-sitter-tlaplus/actions/workflows/ci.yml/badge.svg)](https://github.com/tlaplus-community/tree-sitter-tlaplus/actions/workflows/ci.yml)
[![npm](https://img.shields.io/npm/v/@tlaplus/tree-sitter-tlaplus.svg)](https://www.npmjs.com/package/@tlaplus/tree-sitter-tlaplus)
[![crates.io](https://img.shields.io/crates/v/tree-sitter-tlaplus.svg)](https://crates.io/crates/tree-sitter-tlaplus)
[![pypi][pypi]](https://pypi.org/project/tree-sitter-tlaplus)

## Overview

This is a [tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar for the formal specification language [TLA⁺](https://en.wikipedia.org/wiki/TLA%2B) and its embedded variant [PlusCal](https://en.wikipedia.org/wiki/PlusCal).
Tree-sitter is an incremental error-tolerant parser generator primarily aimed at language tooling such as highlighting, code folding, symbol finding, and other tasks making use of its fully-featured syntax tree query API.
This grammar is intended to function gracefully while parsing a source file mid-edit, when the syntax isn't fully correct.
It is also fast enough to re-parse the file on every keystroke.
You can take the parser for a spin at https://tlaplus-community.github.io/tree-sitter-tlaplus/

The most important files in this repo are `grammar.js` and `src/scanner.c`.
The former is the source of truth for parser code generation and the latter contains logic for parsing the context-sensitive parts of TLA⁺ like nested proofs and conjunction/disjunction lists.
This grammar is published as a [Rust crate](https://crates.io/crates/tree-sitter-tlaplus), [Node.js package](https://www.npmjs.com/package/@tlaplus/tree-sitter-tlaplus), and [Python package](https://pypi.org/project/tree-sitter-tlaplus).
You can see examples of how to consume these packages [here](test/consumers).
A WASM build is also included in the Node.js package and attached to the releases in this repo.

A blog post detailing the development process of this parser can be found [here](https://ahelwer.ca/post/2023-01-11-tree-sitter-tlaplus/).
This repo is [mirrored on sourcehut](https://git.sr.ht/~ahelwer/tree-sitter-tlaplus).

## Aims & Capabilities

The aim of this project is to facilitate creation of modern user-assistive language tooling for TLA⁺.
To that end, the project provides two main capabilities:
1. Provide an approximately-correct parse tree for TLA⁺ specifications in standardized form, for easy integration with general projects designed to consume the tree-sitter grammars of many languages.
1. Provide a [tree query API](https://tree-sitter.github.io/tree-sitter/using-parsers#pattern-matching-with-queries) for efficiently querying the TLA⁺ parse tree, in addition to an API for arbitrary programmatic exploration of same, with bindings in multiple languages for easy integration with projects specifically targeting TLA⁺.

The correctness criterion of this parser is as follows: if the TLA⁺ specification being parsed constitutes valid TLA⁺ (both syntactically and semantically), the parse tree will be correct.
If the spec is not valid TLA⁺, the parse tree will be approximately correct - perhaps permissively allowing illegal syntax, or interpreting erroneous syntax in strange ways.
This permissive behavior makes it excellent for user-assistive language tooling, but a less-compelling choice as the backbone for an interpreter or model-checker.
Application possibilities include:
 * Advanced syntax highlighting
 * Syntax-aware code folding
 * Lightweight backend for a TLA⁺ [language server](https://microsoft.github.io/language-server-protocol/)
 * Writing TLA⁺ specs via dictation using [Cursorless](https://github.com/pokey/cursorless-vscode)
 * Semantic analysis of TLA⁺ specs [on GitHub](https://github.com/github/semantic)
 * Translation of TLA⁺ operator symbols [into their unicode equivalents](https://github.com/tlaplus-community/tlauc)

## Use & Notable Integrations

There are a number of avenues available for consuming & using the parser in a project of your own; see examples in several different programming languages [here](test/consumers).

Notable projects currently using or integrating this grammar include:
 * [nvim-treesitter](https://github.com/nvim-treesitter/nvim-treesitter) for TLA⁺ syntax highlighting & code folding in Neovim
 * [tla-web](https://github.com/will62794/tla-web) for a web-based TLA⁺ interpreter and trace explorer
 * GitHub for syntax highlighting of TLA⁺ files and snippets
 * [tlauc](https://github.com/tlaplus-community/tlauc) for translating between ASCII and Unicode TLA⁺ symbols

As applicable, query files for integrations live in the `integrations` directory.

## Build & Test

Be sure to clone the repo with the `--recurse-submodules` parameter, or run `git submodule update --init --recursive` if you already cloned it without that parameter.

If using nix:
1. Run `nix-shell`
1. Run `tree-sitter test`

Otherwise:
1. Install [node.js and npm](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm)
1. Ensure a C compiler is installed and on your path
1. Run `npm install`
1. Run `npm test`

### Corpus Tests

This test ensures the grammar can parse all modules in the [tlaplus/examples](https://github.com/tlaplus/examples) repo, which is included as a git submodule.
To run:
1. If this is the first time running tree-sitter on your machine, run `npx tree-sitter init-config`
1. For Unix-type OSs, run `./test/run-corpus.sh`; for Windows, run `.\test\run-corpus.ps1`
1. The scripts exit with error code 0 if successful

### Build WASM & Start Playground

If using nix:
1. Run `nix-shell`
1. Run `tree-sitter build-wasm`
1. Start the playground with `tree-sitter playground`

Otherwise:
1. Install [node.js and npm](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm)
1. Install [Emscripten 3.x](https://emscripten.org/)
1. Run `npm install`
1. Run `npx tree-sitter build-wasm`
1. Start the playground with `npx tree-sitter playground`

The playground enables you to easily try out the parser in your browser.
You can use the playground [online](https://tlaplus-community.github.io/tree-sitter-tlaplus/) (serving the latest release) or run it locally by following the directions above.

The playground consists of a pane containing an editable TLA⁺ spec, and another pane containing the parse tree for that spec.
The parse tree is updated in real time as you edit the TLA⁺ spec.
You can click parse tree nodes to highlight the corresponding snippet of TLA⁺, and move the cursor around the spec to show the corresponding parse tree node.
You can click the "log" checkbox and open your browser's development console to see the parser's debug output as it attempts to parse the TLA⁺ spec.
You can also click the "query" checkbox to open a third pane for testing [tree queries](https://tree-sitter.github.io/tree-sitter/using-parsers#pattern-matching-with-queries); for example, enter the following to match all operator names in a capture named `@operator` (indicated by the names becoming highlighted):
```
(operator_definition name: (identifier) @operator)
```

## Fuzzing

You can fuzz the grammar if you're running Linux with a recent version of Clang installed.
Do so as follows:
1. Clone the repo with the `--recurse-submodules` parameter
2. From repo root, run the bash script `test/fuzzing/build-for-fuzzing.sh`
3. From repo root, run `test/fuzzing/out/tree_sitter_tlaplus_fuzzer`

## Contributions

One easy way to contribute is to add your TLA⁺ specifications to the [tlaplus/examples](https://github.com/tlaplus/examples) repo, which this grammar uses as a valuable test corpus!

Pull requests are welcome. If you modify `grammar.js`, make sure you run `npx tree-sitter generate` before committing & pushing.
Generated files are (unfortunately) currently present in the repo but will hopefully be removed in [the future](https://github.com/tree-sitter/tree-sitter/discussions/1243).
Their correspondence is enforced during CI.

