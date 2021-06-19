#include <tree_sitter/parser.h>
#include <cassert>
#include <cstring>
#include <vector>

namespace {

  /**
   * Tokens emitted by this external scanner.
   */
  enum TokenType {
    INDENT,   // Marks beginning of junction list.
    NEWLINE,  // Separates items of junction list.
    DEDENT    // Marks end of junction list.
  };

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

  bool is_whitespace(int32_t codepoint) {
    return codepoint == ' '
      || codepoint == '\t'
      || codepoint == '\n'
      || codepoint == '\r';
  }

  /**
   * Symmetrical delimiters encountered in TLA+.
   */
  enum DelimiterType {
    L_PARENTHESIS,    // (
    R_PARENTHESIS,    // )
    L_SQUARE_BRACKET, // [
    R_SQUARE_BRACKET, // ]
    L_CURLY_BRACE,    // {
    R_CURLY_BRACE,    // }
    L_ANGLE_BRACKET,  // << or 〈 
    R_ANGLE_BRACKET,  // >> or 〉
    NOT_A_DELIMITER   // None of the above.
  };

  DelimiterType delimiter_type(TSLexer* lexer) {
    switch (next_codepoint(lexer)) {
      case '(': return L_PARENTHESIS;
      case ')': return R_PARENTHESIS;
      case '[': return L_SQUARE_BRACKET;
      case ']': return R_SQUARE_BRACKET;
      case '{': return L_CURLY_BRACE;
      case '}': return R_CURLY_BRACE;
      case '〈': return L_ANGLE_BRACKET;
      case '〉': return R_ANGLE_BRACKET;
      case '<':
        lexer->mark_end(lexer);
        advance(lexer);
        if (next_codepoint_is(lexer, '<')) return L_ANGLE_BRACKET;
        else return NOT_A_DELIMITER;  // Less-than operator.
      case '>':
        lexer->mark_end(lexer);
        advance(lexer);
        if (next_codepoint_is(lexer, '>')) return R_ANGLE_BRACKET;
        else return NOT_A_DELIMITER;  // Greater-than operator.
      default: return NOT_A_DELIMITER;
    }
  }

  bool is_left_delimiter(const DelimiterType delimiter) {
    return delimiter == L_PARENTHESIS
      || delimiter == L_SQUARE_BRACKET
      || delimiter == L_CURLY_BRACE
      || delimiter == L_ANGLE_BRACKET;
  }

  bool is_right_delimiter(const DelimiterType delimiter) {
    return delimiter == R_PARENTHESIS
      || delimiter == R_SQUARE_BRACKET
      || delimiter == R_CURLY_BRACE
      || delimiter == R_ANGLE_BRACKET;
  }

  bool delimiter_match(const DelimiterType left, const DelimiterType right) {
    return (left == L_PARENTHESIS && right == R_PARENTHESIS)
      || (left == L_SQUARE_BRACKET && right == R_SQUARE_BRACKET)
      || (left == L_CURLY_BRACE && right == R_CURLY_BRACE)
      || (left == L_ANGLE_BRACKET && right == R_ANGLE_BRACKET);
  }

  using column_index = int16_t;

  enum JunctType {
    CONJUNCTION,
    DISJUNCTION
  };

  struct JunctList {
    JunctType type;
    column_index alignment_column;
    std::vector<DelimiterType> contained_delimiters;

    JunctList() { }

    JunctList(JunctType type, column_index alignment_column) {
      this->type = type;
      this->alignment_column = alignment_column;
    }

    unsigned serialize(char* buffer) {
      size_t offset = 0;
      size_t byte_count = 0;
      size_t copied = 0;

      // Serialize junction type
      copied = sizeof(uint8_t);
      buffer[offset] = static_cast<uint8_t>(type);
      offset += copied;
      byte_count += copied;

      // Serialize alignment column
      copied = sizeof(column_index);
      memcpy(&buffer[offset], (char*)&alignment_column, copied);
      offset += copied;
      byte_count += copied;

      // Serialize delimiters
      const size_t delimiter_count = contained_delimiters.size();
      assert(delimiter_count <= UINT8_MAX);
      copied = sizeof(uint8_t);
      buffer[offset] = static_cast<uint8_t>(delimiter_count);
      offset += copied;
      byte_count += copied;
      for (int i = 0; i < delimiter_count; i++) {
        copied = sizeof(uint8_t);
        buffer[offset] = static_cast<uint8_t>(contained_delimiters[i]);
        offset += copied;
        byte_count += copied;
      }

      return byte_count;
    }

    unsigned deserialize(const char* buffer, const unsigned length) {
      size_t byte_count = 0;
      size_t offset = 0;
      size_t copied = 0;

      // Deserialize junction type
      copied = sizeof(uint8_t);
      type = JunctType(buffer[offset]);
      offset += copied;
      byte_count += copied;

      // Deserialize alignment column
      copied = sizeof(column_index);
      memcpy((char*)&alignment_column, &buffer[offset], copied);
      offset += copied;
      byte_count += copied;

      // Deserialize delimiters
      copied = sizeof(uint8_t);
      const size_t delimiter_count = static_cast<size_t>(buffer[offset]);
      offset += copied;
      byte_count += copied;
      contained_delimiters.resize(delimiter_count);
      for (int i = 0; i < delimiter_count; i++) {
        copied = sizeof(uint8_t);
        contained_delimiters.push_back(DelimiterType(buffer[offset]));
        offset += copied;
        byte_count += copied;
      }

      return byte_count;
    }
  };


  struct Scanner {
    std::vector<JunctList> jlists;

    Scanner() {
      deserialize(NULL, 0);
    }

    // Support nested conjlists up to 256 deep
    unsigned serialize(char* buffer) {
      size_t offset = 0;
      size_t byte_count = 0;
      size_t copied = 0;

      const size_t jlist_depth = jlists.size();
      assert(jlist_depth <= UINT8_MAX);
      copied = sizeof(uint8_t);
      buffer[offset] = static_cast<uint8_t>(jlist_depth);
      offset += copied;
      byte_count += copied;
      for (int i = 0; i < jlist_depth; i++) {
        copied = jlists[i].serialize(&buffer[offset]);
        offset += copied;
        byte_count += copied;
      }

      return byte_count;
    }

    void deserialize(const char* buffer, const unsigned length) {
      if (length > 0) {
        size_t offset = 0;
        size_t copied = 0;

        copied = sizeof(uint8_t);
        const size_t jlist_depth = buffer[offset];
        jlists.resize(jlist_depth);
        offset += copied;
        for (int i = 0; i < jlist_depth; i++) {
          assert(offset <= length);
          copied = jlists[i].deserialize(&buffer[offset], length - offset);
          offset += copied;
        }
      }
    }

    column_index get_current_jlist_column_index() {
      return this->jlists.empty()
        ? -1 : this->jlists.back().alignment_column;
    }

    void push_delimiter(const DelimiterType type) {
      if (!jlists.empty()) {
        jlists.back().contained_delimiters.push_back(type);
      }
    }

    std::vector<int32_t> next_token(TSLexer* lexer) {
      std::vector<int32_t> token;
      while (has_next(lexer)) {
        int32_t codepoint = next_codepoint(lexer);
        if (is_whitespace(codepoint)) {
          if (token.empty()) {
            skip(lexer);
          } else {
            return token;
          }
        } else {
          if (token.empty()) {
            lexer->mark_end(lexer);
          }

          token.push_back(codepoint);
          advance(lexer);
        }
      }
    }

    void emit_indent(TSLexer* lexer, column_index next) {
      lexer->result_symbol = INDENT;
      JunctList new_list(CONJUNCTION, next);
      this->jlists.push_back(new_list);
    }

    void emit_dedent(TSLexer* lexer) {
      lexer->result_symbol = DEDENT;
      this->jlists.pop_back();
    }

    /**
     * Conjlists are identified with the column position (cpos) of the first
     * land token in the list. For a given conjunct, there are four cases:
     * 1. The conjunct is after the cpos of the current conjlist, and an
     *    INDENT token is expected
     *    -> this is a new nested conjlist, emit INDENT token
     * 2. The conjunct is after the cpos of the current conjlist, and an
     *    INDENT token is *not* expected
     *    -> this is an infix land operator; emit nothing
     * 3. The conjunct is equal to the cpos of the current conjlist
     *    -> this is an item of the current conjlist; emit NEWLINE token
     * 4. The conjunct is prior to the cpos of the current conjlist
     *    -> this ends the current conjlist, emit DEDENT token
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param valid_symbols Tokens possibly expected in this spot.
     * @param next The column position of the land token encountered.
     * @return Whether a jlist-relevant token should be emitted.
     */
    bool handle_land_token(
      TSLexer* lexer,
      const bool* valid_symbols,
      const column_index next
    ) {
      const column_index current = get_current_jlist_column_index();
      if (current < next) {
        if (valid_symbols[INDENT]) {
          emit_indent(lexer, next);
          return true;
        } else {
          return false;
        }
      } else if (current == next) {
        assert(valid_symbols[NEWLINE]);
        lexer->result_symbol = NEWLINE;
        return true;
      } else {
        assert(valid_symbols[DEDENT]);
        emit_dedent(lexer);
        return true;
      }
    }

    /**
     * Non-land tokens could possibly indicate the end of a conjlist. Rules:
     * - If the token cpos is leq to the current conjlist cpos, the conjlist
     *   has ended; emit a DEDENT token (possibly multiple).
     * - If the cpos is gt the current conjlist cpos and the token is one of
     *   the following:
     *   1. A right delimiter matching some left delimiter that occurred
     *      *before* the beginning of the current conjlist; includes ),
     *      ], }, and >>
     *   2. The beginning of the next module unit (ex. op == expr)
     *   then emit a DEDENT token (possibly multiple).
     * - Otherwise the token is treated as part of the expression in that
     *   conjunct; for example:
     *       /\ IF e THEN P
     *               ELSE Q
     *       /\ R
     *   so emit no token.
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param next The column position of the non-land token encountered.
     * @return Whether a jlist-relevant token should be emitted.
     */
    bool handle_non_land_token(
      TSLexer* lexer,
      const bool* valid_symbols,
      const column_index next
    ) {
      const column_index current = get_current_jlist_column_index();
      if (next <= current) {
        // TODO: handle parentheses nonsense here.
        assert(valid_symbols[DEDENT]);
        emit_dedent(lexer);
        return true;
      } else {
        const DelimiterType delimiter = delimiter_type(lexer);
        if (is_left_delimiter(delimiter)) {
          push_delimiter(delimiter);
          return false;
        } else if (is_right_delimiter(delimiter)) {
          if (!jlists.empty()) {
            if (jlists.back().contained_delimiters.empty()) {
              emit_dedent(lexer);
              return true;
            } else {
              if (delimiter_match(delimiter, jlists.back().contained_delimiters.back())) {
                jlists.back().contained_delimiters.pop_back();
              } else {
                // Mismatched delimiters! This is a parse error.
                // Do nothing; let tree-sitter handle error recovery.
                return false;
              }
            }
          } else {
            // Not in jlist; ignore this delimiter.
            return false;
          }
        } else /* NOT_A_DELIMITER */ {
          // TODO check for unit definition
          return false;
        }
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
              const column_index col = lexer->get_column(lexer);
              lexer->mark_end(lexer);
              return handle_land_token(lexer, valid_symbols, col);
            } case '/': {
              const column_index col = lexer->get_column(lexer);
              lexer->mark_end(lexer);
              advance(lexer);
              if (next_codepoint_is(lexer, '\\')) {
                return handle_land_token(lexer, valid_symbols, col);
              } else {
                // This is probably the division infix operator.
                return handle_non_land_token(lexer, valid_symbols, col);
              }
            } default: {
              const column_index col = lexer->get_column(lexer);
              return handle_non_land_token(lexer, valid_symbols, col);
            }
          }
        }

        // Emit DEDENT if have reached EOF while in jlist.
        if (valid_symbols[DEDENT]) {
          emit_dedent(lexer);
          return true;
        }
      }

      return false;
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
