const Parser = require('tree-sitter');
const TLA = require('@tlaplus/tree-sitter-tlaplus');
const fs = require('fs');

const parser = new Parser();
parser.setLanguage(TLA);

const sourceCode = `
---- MODULE Test ----
op ≜ ∀ n ∈ ℕ : n ≥ 0
====`;

const tree = parser.parse(sourceCode);

const callExpression = tree.rootNode.toString();
console.log(callExpression)

