# Adapted from https://github.com/tree-sitter/tree-sitter/blob/master/test/fuzz/gen-dict.py
# MIT License Copyright (c) 2018-2021 Max Brunsfeld

import json
import sys

def find_literals(literals, node):
  '''Recursively find STRING literals in the grammar definition'''

  if type(node) is dict:
    if 'type' in node and node['type'] == 'STRING' and 'value' in node:
      literals.add(node['value'])

    for _, value in node.items():
      find_literals(literals, value)

  elif type(node) is list:
    for item in node:
      find_literals(literals, item)

def main():
  '''Generate a libFuzzer / AFL dictionary from a tree-sitter grammar.json'''
  with open(sys.argv[1]) as f:
    grammar = json.load(f)

  literals = set()
  find_literals(literals, grammar['rules'])

  for literal in sorted(literals):
    print('"%s"' % ''.join(['\\x%02x' % codepoint for codepoint in literal.encode('utf-8')]))

if __name__ == '__main__':
  main()

