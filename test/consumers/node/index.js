const Parser = require('tree-sitter');
const { Query } = Parser
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

const query = new Query(TLA, '(def_eq "≜") @capture')
console.log(query.captures(tree.rootNode))

