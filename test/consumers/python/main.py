import tree_sitter_tlaplus as tstla
from tree_sitter import Language, Parser

TLAPLUS_LANGUAGE = Language(tstla.language())
parser = Parser(TLAPLUS_LANGUAGE)
tree = parser.parse(bytes("""
---- MODULE Test ----
op ≜ ∀ n ∈ ℕ : n ≥ 0
====
""", "utf8"))
print(tree.root_node)

query = TLAPLUS_LANGUAGE.query('(def_eq \"≜\") @capture')
captures = query.captures(tree.root_node)
print(captures['capture'])

