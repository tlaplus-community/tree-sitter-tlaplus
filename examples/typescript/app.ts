import Parser = require('tree-sitter');
//@ts-ignore
import TlaPlus = require('@tlaplus/tree-sitter-tlaplus');

const parser : Parser = new Parser();
parser.setLanguage(TlaPlus);
const source : string = `
---- MODULE Test ----
f(x) == x
====
`;
const tree : Parser.Tree = parser.parse(source);
console.log(tree.rootNode.toString())
