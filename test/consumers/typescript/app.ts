import {default as Parser} from 'tree-sitter';
//@ts-ignore
import TlaPlus = require('@tlaplus/tree-sitter-tlaplus');

const parser : Parser = new Parser();
parser.setLanguage(TlaPlus);
const source : string = `
---- MODULE Test ----
op ≜ ∀ n ∈ ℕ : n ≥ 0
===="#;
`;
const tree : Parser.Tree = parser.parse(source);
console.log(tree.rootNode.toString());

