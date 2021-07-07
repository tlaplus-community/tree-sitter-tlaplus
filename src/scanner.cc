#include <tree_sitter/parser.h>
#include <cassert>
#include <vector>
#include <cstring>

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
  void advance(TSLexer* const lexer) {
    lexer->advance(lexer, false);
  }

  /**
   * Advances the scanner while marking the codepoint as whitespace.
   * 
   * @param lexer The tree-sitter lexing control structure.
   */
  void skip(TSLexer* const lexer) {
    lexer->advance(lexer, true);
  }

  /**
   * Gets the next codepoint in the string.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @return The next codepoint in the string.
   */
  int32_t next_codepoint(const TSLexer* const lexer) {
    return lexer->lookahead;
  }

  /**
   * Checks whether the next codepoint is the one given.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param codepoint The codepoint to check.
   * @return Whether the next codepoint is the one given.
   */
  bool next_codepoint_is(
    const TSLexer* const lexer,
    int32_t const codepoint
  ) {
    return codepoint == next_codepoint(lexer);
  }

  /**
   * Checks whether there are any codepoints left in the string.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @return Whether there are any codepoints left in the string.
   */
  bool has_next(const TSLexer* const lexer) {
    return !next_codepoint_is(lexer, 0);
  }

  /**
   * Checks whether the given codepoint is whitespace.
   * 
   * @param codepoint The codepoint to check.
   * @return Whether the given codepoint is whitespace.
   */
  bool is_whitespace(int32_t const codepoint) {
    return codepoint == ' '
      || codepoint == '\t'
      || codepoint == '\n'
      || codepoint == '\r';
  }

  /**
   * Checks whether the next token is the one given.
   * A token is a sequence of codepoints.
   * This function can change the state of the lexer.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @return Whether the next token is the one given.
   */
  bool is_next_token(
    TSLexer* const lexer,
    const std::vector<int32_t>& token
  ) {
    for (auto codepoint : token) {
      if (!next_codepoint_is(lexer, codepoint)) {
        return false;
      }

      advance(lexer);
    }

    return true;
  }

  /**
   * Checks whether the next token is a module-level unit.
   * TODO: implement this logic
   * 
   * @param lexer the tree-sitter lexing control structure.
   * @return Whether the next token is a unit.
   */
  bool is_next_token_unit(TSLexer* const lexer) {
    return false;
  }

  /**
   * Consumes whitespace until it encounters a non-whitespace codepoint.
   * 
   * @param lexer The tree-sitter lexing control structure.
   */
  void consume_whitespace(TSLexer* const lexer) {
    while (is_whitespace(next_codepoint(lexer))) {
      skip(lexer);
    }
  }

  /**
   * Interesting token types for the purpose of parsing junctlists.
   */
  enum LookaheadTokenType {
    LAND,             // /\ or ∧
    LOR,              // \/ or ∨
    RIGHT_DELIMITER,  // ), ], }, 〉, or >>
    UNIT,             // op == expr, etc.
    MODULE_END,       // ====
    END_OF_FILE,      // The end of the file.
    OTHER             // Tokens not requiring special handling logic.
  };

  static const std::vector<int32_t> LAND_TOKEN = {'/', '\\'};
  static const std::vector<int32_t> LOR_TOKEN = {'\\', '/'};
  static const std::vector<int32_t> R_ANGLE_BRACKET_TOKEN = {'>', '>'};
  static const std::vector<int32_t> MODULE_END_TOKEN = {'=', '=', '=', '='};
  static const std::vector<int32_t> THEN_TOKEN = {'T', 'H', 'E', 'N'};
  static const std::vector<int32_t> ELSE_TOKEN = {'E', 'L', 'S', 'E'};
  static const std::vector<int32_t> CASE_ARROW_TOKEN = {'-', '>'};

  using column_index = int16_t;

  /**
   * Scans for & identifies the next interesting token.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param out_col Out parameter; the column of the identified token.
   * @return The type of token identified.
   */
  LookaheadTokenType get_next_token(
    TSLexer* const lexer,
    column_index& out_col
  ) {
    consume_whitespace(lexer);
    lexer->mark_end(lexer);
    out_col = lexer->get_column(lexer);

    if (!has_next(lexer)) {
      return END_OF_FILE;
    }

    switch (next_codepoint(lexer)) {
      case L'∧': return LAND;
      case '/': return is_next_token(lexer, LAND_TOKEN) ? LAND : OTHER;
      case L'∨': return LOR;
      case '\\': return is_next_token(lexer, LOR_TOKEN) ? LOR : OTHER;
      case ')': return RIGHT_DELIMITER;
      case ']': return RIGHT_DELIMITER;
      case '}': return RIGHT_DELIMITER;
      case L'〉': return RIGHT_DELIMITER;
      case 'T': // IF/THEN
        return is_next_token(lexer, THEN_TOKEN)
          ? RIGHT_DELIMITER : OTHER;
      case 'E': // THEN/ELSE
        return is_next_token(lexer, ELSE_TOKEN)
          ? RIGHT_DELIMITER : OTHER;
      case '-': // CASE/-> or []/->
        return is_next_token(lexer, CASE_ARROW_TOKEN)
          ? RIGHT_DELIMITER : OTHER;
      case '>':
        return is_next_token(lexer, R_ANGLE_BRACKET_TOKEN)
          ? RIGHT_DELIMITER : OTHER;
      case '=':
        return is_next_token(lexer, MODULE_END_TOKEN)
          ? MODULE_END : OTHER;
      default:
        return is_next_token_unit(lexer) ? UNIT : OTHER;
    }
  }

  enum JunctType {
    CONJUNCTION,
    DISJUNCTION
  };

  struct JunctList {
    JunctType type;
    column_index alignment_column;

    JunctList() { }

    JunctList(JunctType const type, column_index const alignment_column) {
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

    unsigned deserialize(const char* const buffer, unsigned const length) {
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


  /**
   * A stateful scanner used to parse junction lists.
   */
  struct Scanner {
    /**
     * The nested junction lists at the current lexer position.
     */
    std::vector<JunctList> jlists;

    /**
     * Initializes a new instance of the Scanner object.
     */
    Scanner() {
      deserialize(NULL, 0);
    }

    /**
     * Serializes the Scanner state into the given buffer.
     *
     * @param buffer The buffer into which to serialize the scanner state.
     * @return Number of bytes written into the buffer.
     */
    unsigned serialize(char* const buffer) {
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
      for (size_t i = 0; i < jlist_depth; i++) {
        copied = jlists[i].serialize(&buffer[offset]);
        offset += copied;
        byte_count += copied;
      }

      return byte_count;
    }

    /**
     * Deserializes the Scanner state from the given buffer.
     * 
     * @param buffer The buffer from which to deserialize the state.
     * @param length The bytes available to read from the buffer.
     */
    void deserialize(const char* const buffer, unsigned const length) {
      jlists.clear();
      if (length > 0) {
        size_t offset = 0;
        size_t copied = 0;

        copied = sizeof(uint8_t);
        const size_t jlist_depth = buffer[offset];
        jlists.resize(jlist_depth);
        offset += copied;
        for (size_t i = 0; i < jlist_depth; i++) {
          assert(offset < length);
          copied = jlists[i].deserialize(&buffer[offset], length - offset);
          offset += copied;
        }

        assert(offset == length);
      }
    }

    /**
     * Whether the Scanner state indicates we are currently in a jlist.
     * 
     * @return Whether we are in a jlist.
     */
    bool is_in_jlist() {
      return !jlists.empty();
    }

    /**
     * The column index of the current jlist. Returns negative number if
     * we are not currently in a jlist.
     * 
     * @return The column index of the current jlist.
     */
    column_index get_current_jlist_column_index() {
      return is_in_jlist() ? this->jlists.back().alignment_column : -1;
    }

    /**
     * Whether the given jlist type matches the current jlist.
     * 
     * @param type The jlist type to check.
     * @return Whether the given jlist type matches the current jlist.
     */
    bool current_jlist_type_is(JunctType const type) {
      return this->jlists.empty()
        ? false : type == this->jlists.back().type;
    }

    /**
     * Emits an INDENT token, recording the new jlist in the Scanner state.
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param type The type of the new jlist.
     * @param col The column position of the new jlist.
     * @return Whether an INDENT token was emitted.
     */
    bool emit_indent(
      TSLexer* const lexer,
      JunctType const type,
      column_index const col
    ) {
      lexer->result_symbol = INDENT;
      JunctList new_list(type, col);
      this->jlists.push_back(new_list);
      return true;
    }

    /**
     * Emits a NEWLINE token, marking the start of a new entry in the
     * current jlist.
     *
     * @param lexer The tree-sitter lexing control structure.
     * @return Whether a NEWLINE token was emitted.
     */
    bool emit_newline(TSLexer* const lexer) {
      lexer->result_symbol = NEWLINE;
      return true;
    }

    /**
     * Emits a DEDENT token, removing a jlist from the Scanner state.
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @return Whether a DEDENT token was emitted.
     */
    bool emit_dedent(TSLexer* const lexer) {
      lexer->result_symbol = DEDENT;
      this->jlists.pop_back();
      return true;
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
      TSLexer* const lexer,
      const bool* const valid_symbols,
      JunctType const next_type,
      column_index const next_col
    ) {
      const column_index current_col = get_current_jlist_column_index();
      if (current_col < next_col) {
        if (valid_symbols[INDENT]) {
          /**
           * The start of a new junction list!
           */
          return emit_indent(lexer, next_type, next_col);
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
        if (current_jlist_type_is(next_type)) {
          /**
           * This is another entry in the jlist.
           */
          assert(valid_symbols[NEWLINE]);
          return emit_newline(lexer);
        } else {
          /** 
           * Disjunct in alignment with conjunct list or vice-versa; treat
           * this as an infix operator by terminating the current list.
           */
          assert(valid_symbols[DEDENT]);
          return emit_dedent(lexer);
        }
      } else {
        /**
         * Junct found prior to the alignment column of the current jlist.
         * This marks the end of the jlist.
         */
        assert(valid_symbols[DEDENT]);
        return emit_dedent(lexer);
      }
    }

    /**
     * If a given right delimiter matches some left delimiter that occurred
     * *before* the beginning of the current jlist, then that ends the
     * current jlist. The concept of a delimiter is not limited (hah) to
     * (), [], <<>>, and {}; it also includes IF/THEN, THEN/ELSE, CASE/->,
     * and basically every other language construct where an expression is
     * squeezed between a known start & end token.
     * 
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
     * There are a few notable exceptions to this rule; for example, the
     * empty set or empty sequence:
     * 
     *    /\  { }
     *         ^
     *    /\ << >>
     *         ^ there is the option for an expression here, so tree-sitter
     *           looks for INDENT tokens and we will see a right delimiter
     *           in this external scanner.
     * 
     * Another example when the code is in a non-parseable state which we
     * nonetheless wish to handle gracefully:
     * 
     *    /\ [x \in S |-> ]
     *                   ^ user is about to write an expression here, but
     *                     there is a time when the code is non-parseable;
     *                     tree-sitter will again look for an INDENT token
     *                     and we will see a right delimiter in this
     *                     external scanner.
     * 
     * The easy solution to these cases is to simply check whether
     * tree-sitter is looking for a DEDENT token. If so, emit one; if not,
     * emit nothing. Tree-sitter will not look for a DEDENT token inside
     * enclosing delimiters within the scope of a jlist.
     * 
     * One side-effect of all this is that tree-sitter parses certain
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
     * 
     * This should simply be detected as an error at the semantic level.
     */
    bool handle_right_delimiter_token(
      TSLexer* const lexer,
      const bool* const valid_symbols,
      column_index const next
    ) {
      return is_in_jlist()
        && valid_symbols[DEDENT]
        && emit_dedent(lexer);
    }

    /**
     * Emits a dedent token if are in jlist and have encountered a token that
     * unconditionally ends a jlist regardless of column position; these
     * include:
     * 1. New unit definition (op == expr, etc.)
     * 2. End-of-module token (====)
     * 3. End-of-file (this shouldn't happen but we will end the jlist to
     *    improve error reporting since the end-of-module token is missing)
     */
    bool handle_terminator_token(
      TSLexer* const lexer,
      const bool* const valid_symbols
    ) {
      if (is_in_jlist()) {
        assert(valid_symbols[DEDENT]);
        return emit_dedent(lexer);
      } {
        return false;
      }
    }

    /**
     * Non-junct tokens could possibly indicate the end of a jlist. Rules:
     * - If the token cpos is leq to the current jlist cpos, the jlist
     *   has ended; emit a DEDENT token (possibly multiple); example:
     *      IF  /\ P
     *          /\ Q
     *      THEN R
     *      ELSE S
     * - Otherwise the token is treated as part of the expression in that
     *   junct; for example:
     *      /\ IF e THEN P
     *              ELSE Q
     *      /\ R
     *   so emit no token.
     * 
     * @param lexer The tree-sitter lexing control structure.
     * @param next The column position of the token encountered.
     * @return Whether a jlist-relevant token should be emitted.
     */
    bool handle_other_token(
      TSLexer* const lexer,
      const bool* const valid_symbols,
      column_index const next
    ) {
      const column_index current = get_current_jlist_column_index();
      if (next <= current) {
        /**
         * Found a token prior to the jlist's start column; this means
         * the current jlist has ended, so emit a DEDENT token.
         */
        assert(valid_symbols[DEDENT]);
        return emit_dedent(lexer);
      } else {
        /**
         * The token encountered must be part of the expression in this
         * jlist item; ignore it.
         */
        return false;
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
    bool scan(TSLexer* const lexer, const bool* const valid_symbols) {
      if (valid_symbols[INDENT]
        || valid_symbols[NEWLINE]
        || valid_symbols[DEDENT]
      ) {
        column_index col;
        switch (get_next_token(lexer, col)) {
          case LAND:
            return handle_junct_token(lexer, valid_symbols, CONJUNCTION, col);
          case LOR:
            return handle_junct_token(lexer, valid_symbols, DISJUNCTION, col);
          case RIGHT_DELIMITER:
            return handle_right_delimiter_token(lexer, valid_symbols, col);
          case UNIT:
            return handle_terminator_token(lexer, valid_symbols);
          case MODULE_END:
            return handle_terminator_token(lexer, valid_symbols);
          case END_OF_FILE:
            return handle_terminator_token(lexer, valid_symbols);
          case OTHER:
            return handle_other_token(lexer, valid_symbols, col);
        }
      }

      return false;
    }
  };
}

extern "C" {

  // Called once when language is set on a parser.
  // Allocates memory for storing scanner state.
  void* tree_sitter_tlaplus_external_scanner_create() {
      return new Scanner();
  }

  // Called once parser is deleted or different language set.
  // Frees memory storing scanner state.
  void tree_sitter_tlaplus_external_scanner_destroy(void* const payload) {
    Scanner* const scanner = static_cast<Scanner*>(payload);
    delete scanner;
  }

  // Called whenever this scanner recognizes a token.
  // Serializes scanner state into buffer.
  unsigned tree_sitter_tlaplus_external_scanner_serialize(
    void* const payload,
    char* const buffer
  ) {
    Scanner* scanner = static_cast<Scanner*>(payload);
    return scanner->serialize(buffer);
  }

  // Called when handling edits and ambiguities.
  // Deserializes scanner state from buffer.
  void tree_sitter_tlaplus_external_scanner_deserialize(
    void* const payload,
    const char* const buffer,
    unsigned const length
  ) {
    Scanner* const scanner = static_cast<Scanner*>(payload);
    scanner->deserialize(buffer, length);
  }

  // Scans for tokens.
  bool tree_sitter_tlaplus_external_scanner_scan(
    void* const payload,
    TSLexer* const lexer,
    const bool* const valid_symbols
  ) {
    Scanner* const scanner = static_cast<Scanner*>(payload);
    return scanner->scan(lexer, valid_symbols);
  }
}
