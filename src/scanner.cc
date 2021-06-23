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

  /**
   * Advances the scanner while marking the codepoint as non-whitespace.
   * 
   * @param lexer The tree-sitter lexing control structure.
   */
  void advance(TSLexer* lexer) {
    lexer->advance(lexer, false);
  }

  /**
   * Advances the scanner while marking the codepoint as whitespace.
   * 
   * @param lexer The tree-sitter lexing control structure.
   */
  void skip(TSLexer* lexer) {
    lexer->advance(lexer, true);
  }

  /**
   * Gets the next codepoint in the string.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @return The next codepoint in the string.
   */
  int32_t next_codepoint(TSLexer* lexer) {
    return lexer->lookahead;
  }

  /**
   * Checks whether the next codepoint is the one given.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param codepoint The codepoint to check.
   * @return Whether the next codepoint is the one given.
   */
  bool next_codepoint_is(TSLexer* lexer, const int32_t codepoint) {
    return codepoint == next_codepoint(lexer);
  }

  /**
   * Checks whether there are any codepoints left in the string.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @return Whether there are any codepoints left in the string.
   */
  bool has_next(TSLexer* lexer) {
    return !next_codepoint_is(lexer, 0);
  }

  /**
   * Checks whether the given codepoint is whitespace.
   * 
   * @param codepoint The codepoint to check.
   * @return Whether the given codepoint is whitespace.
   */
  bool is_whitespace(const int32_t codepoint) {
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

  /**
   * Determines the type of delimiter from the next token in the string.
   * The function also marks the end of the codepoints consumed by the lexer
   * before advancing beyond the first non-whitespace codepoint.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @return The type of delimiter expressed by the next token.
   */
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

  bool is_right_delimiter(const DelimiterType delimiter) {
    return delimiter == R_PARENTHESIS
      || delimiter == R_SQUARE_BRACKET
      || delimiter == R_CURLY_BRACE
      || delimiter == R_ANGLE_BRACKET;
  }

  bool is_unit_definition(TSLexer* lexer) {
    // TODO: write this logic
    return false;
  }

  using column_index = int16_t;

  enum JunctType {
    CONJUNCTION,
    DISJUNCTION,
    NOT_A_JUNCTION
  };

  /**
   * Looks at next token to determine whether it is a junction of some kind.
   * If so:
   * - function sets out_jtype to type of junction
   * - function sets out_token_start_col to start column of junction
   * - function returns true
   * If not:
   * - function sets out_jtype to NOT_A_JUNCTION
   * - function sets out_token_start_col to start column of junction
   * - function returns false
   * The function also marks the end of the codepoints consumed by the lexer
   * before advancing beyond the first non-whitespace codepoint.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param out_jtype Out parameter; the type of junc token.
   * @param out_token_start_col Out parameter; the token's starting column.
   * @return Whether the next token is a junct token.
   */
  bool try_peek_junct_token(
    TSLexer* lexer,
    JunctType& out_jtype,
    column_index& out_token_start_col
  ) {
    const int32_t next = next_codepoint(lexer);
    if (next == '∧') {
      out_jtype = CONJUNCTION;
      out_token_start_col = lexer->get_column(lexer);
      lexer->mark_end(lexer);
      return true;
    } else if (next == '/') {
      out_jtype = CONJUNCTION;
      out_token_start_col = lexer->get_column(lexer);
      lexer->mark_end(lexer);
      advance(lexer);
      return next_codepoint_is(lexer, '\\');
    } else if (next == '∨') {
      out_jtype = DISJUNCTION;
      out_token_start_col = lexer->get_column(lexer);
      lexer->mark_end(lexer);
      return true;
    } else if (next == '\\') {
      out_jtype = DISJUNCTION;
      out_token_start_col = lexer->get_column(lexer);
      lexer->mark_end(lexer);
      advance(lexer);
      return next_codepoint_is(lexer, '/');
    } else {
      out_jtype = NOT_A_JUNCTION;
      out_token_start_col = lexer->get_column(lexer);
      return false;
    }
  }

  struct JunctList {
    JunctType type;
    column_index alignment_column;

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

      return byte_count;
    }

    unsigned deserialize(const char* buffer, const unsigned length) {
      assert(length > 0);

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

      return byte_count;
    }
  };


  struct Scanner {
    std::vector<JunctList> jlists;

    Scanner() {
      deserialize(NULL, 0);
    }

    unsigned serialize(char* buffer) {
      size_t offset = 0;
      size_t byte_count = 0;
      size_t copied = 0;

      // Support nested conjlists up to 256 deep
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
          assert(offset < length);
          copied = jlists[i].deserialize(&buffer[offset], length - offset);
          offset += copied;
        }

        assert(offset == length);
      } else {
        jlists.clear();
      }
    }

    column_index get_current_jlist_column_index() {
      return this->jlists.empty()
        ? -1 : this->jlists.back().alignment_column;
    }

    JunctType get_current_jlist_type() {
      return this->jlists.empty()
        ? NOT_A_JUNCTION : this->jlists.back().type;
    }

    bool is_in_jlist() {
      return !jlists.empty();
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

    void emit_indent(
      TSLexer* lexer,
      const JunctType type,
      const column_index next
    ) {
      lexer->result_symbol = INDENT;
      JunctList new_list(type, next);
      this->jlists.push_back(new_list);
    }

    void emit_dedent(TSLexer* lexer) {
      lexer->result_symbol = DEDENT;
      this->jlists.pop_back();
    }

    /**
     * Jlists are identified with the column position (cpos) of the first
     * junct token in the list, and the junction type. For a given junct
     * token there are five possible interpretations:
     * 1. The junct is after the cpos of the current jlist, and an
     *    INDENT token is expected
     *    -> this is a new nested jlist, emit INDENT token
     * 2. The junct is after the cpos of the current jlist, and an
     *    INDENT token is *not* expected
     *    -> this is an infix junct operator; emit nothing
     * 3. The junct is equal to the cpos of the current jlist, and is
     *    the same junct type (conjunction or disjunction)
     *    -> this is an item of the current jlist; emit NEWLINE token
     * 4. The junct is equal to the cpos of the current jlist, and is
     *    a DIFFERENT junct type (conjunction vs. disjunction)
     *    -> 
     * 5. The junct is prior to the cpos of the current jlist
     *    -> this ends the current jlist, emit DEDENT token
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param valid_symbols Tokens possibly expected in this spot.
     * @param type The type of junction encountered.
     * @param next The column position of the junct token encountered.
     * @return Whether a jlist-relevant token should be emitted.
     */
    bool handle_junct_token(
      TSLexer* lexer,
      const bool* valid_symbols,
      const JunctType next_type,
      const column_index next_col
    ) {
      const column_index current_col = get_current_jlist_column_index();
      if (current_col < next_col) {
        if (valid_symbols[INDENT]) {
          /**
           * The start of a new junction list!
           */
          emit_indent(lexer, next_type, next_col);
          return true;
        } else {
          /**
           * This is an infix junction symbol. Tree-sitter will only look for
           * a new jlist at the start of an expression rule; infix operators
           * occur when joining two expression rules together, so tree-sitter
           * is only looking for either NEWLINE or DEDENT rules. Examples:
           * 
           *   /\ a /\ b
           *       ^ tree-sitter will NEVER look for an INDENT here
           * 
           *   /\ a
           *   /\ b
           *  ^ tree-sitter WILL look for a NEWLINE here
           * 
           *   /\ /\ a
           *     ^ tree-sitter WILL look for an INDENT here
           */
          return false;
        }
      } else if (current_col == next_col) {
        if (get_current_jlist_type() == next_type) {
          /**
           * This is another entry in the jlist.
           */
          assert(valid_symbols[NEWLINE]);
          lexer->result_symbol = NEWLINE;
          return true;
        } else {
          /** 
           * Disjunct in alignment with conjunct list or vice-versa; treat
           * this as an infix operator by terminating the current list.
           */
          assert(valid_symbols[DEDENT]);
          emit_dedent(lexer);
          return true;
        }
      } else {
        /**
         * Junct found prior to the alignment column of the current jlist.
         * This marks the end of the jlist.
         */
        assert(valid_symbols[DEDENT]);
        emit_dedent(lexer);
        return true;
      }
    }

    /**
     * Non-junct tokens could possibly indicate the end of a jlist. Rules:
     * - If the token cpos is leq to the current jlist cpos, the jlist
     *   has ended; emit a DEDENT token (possibly multiple).
     * - If the cpos is gt the current jlist cpos and the token is one of
     *   the following:
     *   1. A right delimiter matching some left delimiter that occurred
     *      *before* the beginning of the current jlist; includes ),
     *      ], }, and >>
     *   2. The beginning of the next module unit (ex. op == expr)
     *   then emit a DEDENT token (possibly multiple).
     * - Otherwise the token is treated as part of the expression in that
     *   junct; for example:
     *       /\ IF e THEN P
     *               ELSE Q
     *       /\ R
     *   so emit no token.
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param next The column position of the non-land token encountered.
     * @return Whether a jlist-relevant token should be emitted.
     */
    bool handle_non_junct_token(
      TSLexer* lexer,
      const bool* valid_symbols,
      const column_index next
    ) {
      const column_index current = get_current_jlist_column_index();
      if (next <= current) {
        /**
         * Found a token prior to the jlist's start column; this means
         * the current jlist has ended, so emit a DEDENT token.
         */
        assert(valid_symbols[DEDENT]);
        emit_dedent(lexer);
        return true;
      } else {
        const DelimiterType delimiter = delimiter_type(lexer);
        if (is_right_delimiter(delimiter)) {
          /**
           * Previously I implemented complicated logic using a stack to keep
           * track of all the delimiters that have been seen (and their
           * pairs) but found that tree-sitter would never trigger the
           * external scanner before encountering a right delimiter matching
           * a left delimiter that started within the scope of a jlist. Thus
           * we can assume that when we *do* see a right delimiter, it
           * matches a left delimiter that occurred prior to the start of the
           * jlist, so we can emit a DEDENT token to end the jlist. Example:
           * 
           *    /\ ( a + b )
           *              ^ tree-sitter will never look for an INDENT,
           *                NEWLINE, or DEDENT token here; it is only
           *                looking for another infix operator or the
           *                right-delimiter.
           * 
           *    ( /\ a + b )
           *              ^ tree-sitter WILL look for an INDENT, NEWLINE, or
           *                DEDENT token here in addition to looking for an
           *                infix operator; it also wants to see a DEDENT
           *                token before seeing the right delimiter, although
           *                error recovery is simple enough that it would
           *                barely notice its absence.
           * 
           * One side-effect of this is that tree-sitter parses certain
           * arrangements of jlists and delimiters that are actually illegal
           * according to TLA+ syntax rules; that is okay since tree-sitter's
           * use case of error-tolerant editor tooling ensures its design
           * errs on the side of being overly-permissive. For a concrete
           * example here, tree-sitter will parse this illegal expression
           * without complaint:
           * 
           *    /\ A
           *    /\ (B + C
           *  )
           *    /\ D
           */
          assert(valid_symbols[DEDENT]);
          emit_dedent(lexer);
          return true;
        } else if (delimiter == NOT_A_DELIMITER && is_unit_definition(lexer)) {
            /**
             * We've encountered a new unit definition, so override all
             * alignment logic and end the jlist.
             */
            assert(valid_symbols[DEDENT]);
            emit_dedent(lexer);
            return true;
        } else {
          /**
           * The token encountered must be part of the expression in this
           * jlist item; ignore it.
           */
          return false;
        }
      }
    }

    /**
     * INDENT tokens are emitted prior to the first junct in a list
     * NEWLINE tokens are emitted between list juncts
     * DEDENT tokens are emitted after the final junct in a list
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param valid_symbols Tokens possibly expected in this spot.
     * @return Whether a token was encountered.
     */
    bool scan(TSLexer* lexer, const bool* valid_symbols) {
      if (valid_symbols[INDENT] || valid_symbols[NEWLINE] || valid_symbols[DEDENT]) {
        while (has_next(lexer)) {
          JunctType jtype;
          column_index col;
          if (is_whitespace(next_codepoint(lexer))) {
            skip(lexer);
          } else if(try_peek_junct_token(lexer, jtype, col)) {
            return handle_junct_token(lexer, valid_symbols, jtype, col);
          } else {
            return is_in_jlist()
              && handle_non_junct_token(lexer, valid_symbols, col);
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
