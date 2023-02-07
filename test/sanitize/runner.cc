#include <cassert>
#include <fstream>
#include "tree_sitter/api.h"

extern "C" const TSLanguage *TS_LANG();

int main(int const argc, char const* const argv[]) {
  auto const file_path = std::string(argv[1]);
  auto file = std::ifstream(file_path);
  std::string const text((std::istreambuf_iterator<char>(file)), std::istreambuf_iterator<char>());

  printf("%s\n", text.c_str());

  TSParser *parser = ts_parser_new();
  bool language_ok = ts_parser_set_language(parser, TS_LANG());
  assert(language_ok);

  TSTree *tree = ts_parser_parse_string(parser, NULL, text.c_str(), text.size());
  TSNode root_node = ts_tree_root_node(tree);

  printf("%s", ts_node_string(root_node));

  ts_tree_delete(tree);
  ts_parser_delete(parser);

  return 0;
}

