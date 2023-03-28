#include <cassert>
#include <fstream>
#include <stdlib.h>
#include "tree_sitter/api.h"

extern "C" const TSLanguage *TS_LANG();

int main(int const argc, char const* const argv[]) {
  bool quiet = argc == 3;

  auto const file_path = std::string(argv[1]);
  auto file = std::ifstream(file_path);
  std::string const text((std::istreambuf_iterator<char>(file)), std::istreambuf_iterator<char>());

  if (!quiet) {
    printf("%s", text.c_str());
  }

  TSParser *parser = ts_parser_new();
  TSLogger *logger = ts_parser_logger(parser);
  logger->log = true;
  bool language_ok = ts_parser_set_language(parser, TS_LANG());
  assert(language_ok);

  TSTree *tree = ts_parser_parse_string(parser, NULL, text.c_str(), text.size());
  TSNode root_node = ts_tree_root_node(tree);

  if (!quiet) {
    char* parse_tree = ts_node_string(root_node);
    printf("%s", parse_tree);
    free(parse_tree);
  }

  ts_tree_delete(tree);
  ts_parser_delete(parser);

  return 0;
}

