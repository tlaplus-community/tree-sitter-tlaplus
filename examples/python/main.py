from tree_sitter import Language, Parser

Language.build_library(
  'build/tree-sitter-languages.so',
  ['../../../tree-sitter-tlaplus']
)

TLAPLUS_LANGUAGE = Language('build/tree-sitter-languages.so', 'tlaplus')
parser = Parser()
parser.set_language(TLAPLUS_LANGUAGE)
tree = parser.parse(bytes("""
---- MODULE Test ----
f(x) == x
====
""", "utf8"))
print(tree.root_node.sexp())
