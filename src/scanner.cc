#include <tree_sitter/parser.h>
#include <cassert>
#include <cstring>
#include <vector>

namespace {

  enum TokenType {
    CONJ_BULLET,
    INDENT,
    DEDENT,
    NEWLINE
  };

  using column_index = uint32_t;

  struct Scanner {
    column_index col;

    Scanner() {
      this->col = 0;
    }

    unsigned serialize(char* buffer) {
      memcpy(buffer, &(this->col), sizeof(column_index));
      return sizeof(column_index);
    }

    void deserialize(const char* buffer, unsigned length) {
      if (0 < length) {
        memcpy(&(this->col), buffer, length);
      }
    }

    void advance(TSLexer* lexer) {
      lexer->advance(lexer, false);
    }

    void skip(TSLexer* lexer) {
      lexer->advance(lexer, true);
    }

    int32_t next_token(TSLexer* lexer) {
      return lexer->lookahead;
    }

    bool next_token_is(TSLexer* lexer, int32_t token) {
      return token == next_token(lexer);
    }

    bool has_next_token(TSLexer* lexer) {
      return !next_token_is(lexer, 0);
    }

    bool next_token_is_one_of(
      TSLexer* lexer,
      const std::vector<int32_t>& tokens
    ) {
      for (int i = 0; i < tokens.size(); i++) {
        if (next_token_is(lexer, tokens[i])) {
          return true;
        }
      }

      return false;
    }

    bool scan(TSLexer* lexer, const bool* valid_symbols) {
      if (valid_symbols[CONJ_BULLET]) {
        while (has_next_token(lexer)) {
          std::vector<int32_t> skip_tokens = {' ', '\t', '\r', '\t'};
          if (next_token_is_one_of(lexer, skip_tokens)) {
            skip(lexer);
          } else if (next_token_is(lexer, '/')) {
            // TODO: get index before or after advancing?
            column_index start_col = lexer->get_column(lexer);
            advance(lexer);
            if (next_token_is(lexer, '\\')) {
              advance(lexer);
              lexer->mark_end(lexer);
              this->col = start_col;
              return true;
            } else {
              return false;
            }
          } else if (next_token_is(lexer, '∧')) {
            this-> col = lexer->get_column(lexer);
            advance(lexer);
            lexer->mark_end(lexer);
            return true;
          } else {
            return false;
          }
        }
      }
    }
  };
}

extern "C" {

  // Called once when language is set on a parser.
  // Allocates memory for storing scanner state.
  void * tree_sitter_tlaplus_external_scanner_create() {
      return new Scanner();
  }

  // Called once parser is deleted or different language set.
  // Frees memory storing scanner state.
  void tree_sitter_tlaplus_external_scanner_destroy(void* payload) {
    Scanner* scanner = static_cast<Scanner*>(payload);
    delete scanner;
  }

  // Called whenever this scanner recognizes a token.
  // Serializes scanner state into buffer.
  unsigned tree_sitter_tlaplus_external_scanner_serialize(
    void* payload,
    char* buffer
  ) {
    Scanner* scanner = static_cast<Scanner*>(payload);
    return scanner->serialize(buffer);
  }

  // Called when handling edits and ambiguities.
  // Deserializes scanner state from buffer.
  void tree_sitter_tlaplus_external_scanner_deserialize(
    void* payload,
    const char* buffer,
    unsigned length
  ) {
    Scanner* scanner = static_cast<Scanner*>(payload);
    scanner->deserialize(buffer, length);
  }

  // Scans for tokens.
  bool tree_sitter_tlaplus_external_scanner_scan(
    void *payload,
    TSLexer *lexer,
    const bool *valid_symbols
  ) {
    Scanner* scanner = static_cast<Scanner*>(payload);
    return scanner->scan(lexer, valid_symbols);
  }
}
