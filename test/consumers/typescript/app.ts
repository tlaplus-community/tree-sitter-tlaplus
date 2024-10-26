import {default as Parser, Query} from 'tree-sitter';
import {default as TlaPlus} from '@tlaplus/tree-sitter-tlaplus';

const parser : Parser = new Parser();
parser.setLanguage(TlaPlus);
const source : string = `
---- MODULE Test ----
op ≜ ∀ n ∈ ℕ : n ≥ 0
===="#;
`;
const tree : Parser.Tree = parser.parse(source);
console.log(tree.rootNode.toString());

const query : Query = new Query(TlaPlus, '(def_eq \"≜\") @capture')
console.log(query.captures(tree.rootNode))

