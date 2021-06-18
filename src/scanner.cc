#include <tree_sitter/parser.h>
#include <cassert>
#include <cstring>
#include <vector>

namespace {

  enum TokenType {
    INDENT,
    NEWLINE,
    DEDENT
  };

  using column_index = int16_t;

  struct Scanner {
    std::vector<column_index> column_indices;

    Scanner() {
      deserialize(NULL, 0);
    }

    // Support nested conjlists up to 256 deep
    // Support column positions up to 2^15
    unsigned serialize(char* buffer) {
      const size_t nested_conjlist_depth = this->column_indices.size();
      assert(nested_conjlist_depth <= UINT8_MAX);
      buffer[0] = static_cast<uint8_t>(nested_conjlist_depth);
      const size_t byte_count = nested_conjlist_depth * sizeof(column_index);
      const size_t length_offset = sizeof(uint8_t);
      if (nested_conjlist_depth > 0) {
        memcpy(&buffer[length_offset], this->column_indices.data(), byte_count);
      }

      return length_offset + byte_count;
    }

    void deserialize(const char* buffer, const unsigned length) {
      if (length > 0) {
        const uint8_t nested_conjlist_depth = buffer[0];
        const size_t byte_count = nested_conjlist_depth * sizeof(column_index);
        const size_t length_offset = sizeof(uint8_t);
        if (nested_conjlist_depth > 0) {
          this->column_indices.resize(nested_conjlist_depth);
          memcpy(this->column_indices.data(), &buffer[length_offset], byte_count);
        }
      }
    }

    void advance(TSLexer* lexer) {
      lexer->advance(lexer, false);
    }

    void skip(TSLexer* lexer) {
      lexer->advance(lexer, true);
    }

    int32_t next_codepoint(TSLexer* lexer) {
      return lexer->lookahead;
    }

    bool next_codepoint_is(TSLexer* lexer, int32_t token) {
      return token == next_codepoint(lexer);
    }

    bool has_next(TSLexer* lexer) {
      return !next_codepoint_is(lexer, 0);
    }

    bool next_codepoint_is_one_of(
      TSLexer* lexer,
      const std::vector<int32_t>& tokens
    ) {
      for (int i = 0; i < tokens.size(); i++) {
        if (next_codepoint_is(lexer, tokens[i])) {
          return true;
        }
      }

      return false;
    }

    /**
     * Conjlists are identified with the column position (cpos) of the first
     * land token in the list. For a given conjunct, there are three cases:
     * 
     * 1. the conjunct is after the cpos of the current conjlist
     *    -> this is a new nested conjlist, emit INDENT token
     * 2. the conjunct is equal to the cpos of the current conjlist
     *    -> this is an item of the current conjlist; emit NEWLINE token
     * 3. the conjunct is prior to the cpos of the current conjlist
     *    -> this ends the current conjlist, emit DEDENT token
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param next The column position of the land token encountered.
     * @return Whether a jlist-relevant token should be emitted.
     */
    bool handle_land(TSLexer* lexer, const column_index next) {
      const column_index current =
        this->column_indices.empty()
        ? -1 : this->column_indices.back();
      if (current < next) {
        lexer->result_symbol = INDENT;
        this->column_indices.push_back(next);
        return true;
      } else if (current == next) {
        lexer->result_symbol = NEWLINE;
        return true;
      } else {
        lexer->result_symbol = DEDENT;
        this->column_indices.pop_back();
        return true;
      }
    }

    /**
    * INDENT tokens are emitted prior to the first conjunct in a list
    * NEWLINE tokens are emitted between list conjuncts
    * DEDENT tokens are emitted after the final conjunct in a list
    * 
    * @param lexer The tree-sitter lexing control structure.
    * @param valid_symbols Tokens possibly expected in this spot.
    * @return Whether a token was encountered.
    */
    bool scan(TSLexer* lexer, const bool* valid_symbols) {
      if (valid_symbols[INDENT] || valid_symbols[NEWLINE] || valid_symbols[DEDENT]) {
        while (has_next(lexer)) {
          switch (next_codepoint(lexer)) {
            case ' ': {
              skip(lexer);
              break;
            } case '\t': {
              skip(lexer);
              break;
            } case '\n': {
              skip(lexer);
              break;
            } case '\r': {
              skip(lexer);
              break;
            } case '∧': {
              const column_index conj_col = lexer->get_column(lexer);
              lexer->mark_end(lexer);
              return handle_land(lexer, conj_col);
            } case '/': {
              const column_index conj_col = lexer->get_column(lexer);
              lexer->mark_end(lexer);
              advance(lexer);
              if (next_codepoint_is(lexer, '\\')) {
                return handle_land(lexer, conj_col);
              } else {
                return false;
              }
            } default: {
              return false;
            }
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
