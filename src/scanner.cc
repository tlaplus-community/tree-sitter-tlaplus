#include <tree_sitter/parser.h>
#include <cassert>
#include <cstring>
#include <vector>

namespace {

  /**
   * Tokens emitted by this external scanner.
   */
  enum TokenType {
    EXTRAMODULAR_TEXT,  // Freeform text between modules.
    BLOCK_COMMENT_TEXT, // Text inside block comments.
    INDENT,             // Marks beginning of junction list.
    NEWLINE,            // Separates items of junction list.
    DEDENT              // Marks end of junction list.
  };

  using token_t = std::vector<int32_t>;

  // All the tokens the external scanner cares about.
  static const token_t BLOCK_COMMENT_START_TOKEN = {'(','*'};
  static const token_t BLOCK_COMMENT_END_TOKEN = {'*',')'};
  static const token_t SINGLE_LINE_TOKEN = {'-','-','-','-'};
  static const token_t MODULE_TOKEN = {'M','O','D','U','L','E'};

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
  bool is_next_codepoint(
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
    return !is_next_codepoint(lexer, 0);
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
   * Checks whether the given codepoint could be used in an identifier,
   * which consist of capital ASCII letters, lowercase ASCII letters,
   * and underscores.
   * 
   * @param codepoint The codepoint to check.
   * @return Whether the given codepoint could be used in an identifier.
   **/
  bool is_identifier_char(int32_t const codepoint) {
    return
      (48 <= codepoint && codepoint <= 57)      // 0-9
      || (65 <= codepoint && codepoint <= 90)   // A-Z
      || (97 <= codepoint && codepoint <= 122)  // a-z
      || 95 == codepoint;                       // _
  }

  /**
   * Consumes codepoints as long as they are whitespace.
   * 
   * @param lexer The tree-sitter lexing control structure.
   **/
  void consume_whitespace(TSLexer* const lexer) {
    while (has_next(lexer) && is_whitespace(next_codepoint(lexer))) {
      skip(lexer);
    }
  }

  /**
   * Consumes codepoints as long as they are the one given.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param codepoint The codepoint to consume.
   * @return The number of codepoints consumed.
   **/
  void consume_codepoint(TSLexer* const lexer, const int32_t codepoint) {
    while (has_next(lexer) && is_next_codepoint(lexer, codepoint)) {
      advance(lexer);
    }
  }

  /**
   * Checks whether the next codepoint sequence is the one given.
   * This function can change the state of the lexer.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param token The codepoint sequence to check for.
   * @return Whether the next codepoint sequence is the one given.
   */
  bool is_next_codepoint_sequence(
    TSLexer* const lexer,
    const token_t& codepoint_sequence
  ) {
    for (int i = 0; i < codepoint_sequence.size(); i++) {
      int32_t codepoint = codepoint_sequence.at(i);
      if (!is_next_codepoint(lexer, codepoint)) {
        return false;
      } else if (i + 1 < codepoint_sequence.size()) {
        advance(lexer);
      }
    }

    return true;
  }

  /**
   * Scans for extramodular text, the freeform text that can be present
   * outside of TLA+ modules. This function skips any leading whitespace
   * to avoid extraneous extramodular text tokens given newlines at the
   * beginning or end of the file. It will consume any text up to the
   * point it performs lookahead that captures the following regex:
   *     /----[-]*[ ]*MODULE/
   * or EOF, which marks the end of the extramodular text. It is important
   * that the extramodular text does not itself include the captured module
   * start sequence, which is why this is in an external scanner rather
   * than a regex in the grammar itself.
   *
   * @param lexer The tree-sitter lexing control structure
   * @return Whether any extramodular text was detected.
   **/
  bool scan_extramodular_text(TSLexer* const lexer) {
    lexer->result_symbol = EXTRAMODULAR_TEXT;
    consume_whitespace(lexer);
    bool has_consumed_any = false;
    while (has_next(lexer)) {
      if (is_next_codepoint(lexer, '-')) {
        lexer->mark_end(lexer);
        if (is_next_codepoint_sequence(lexer, SINGLE_LINE_TOKEN)) {
          consume_codepoint(lexer, '-');
          consume_codepoint(lexer, ' ');
          if (is_next_codepoint_sequence(lexer, MODULE_TOKEN)) {
            return has_consumed_any;
          } else {
            has_consumed_any = true;
          }
        } else {
          has_consumed_any = true;
        }
      } else {
        advance(lexer);
        has_consumed_any = true;
      }
    }

    lexer->mark_end(lexer);
    return has_consumed_any;
  }

  /**
   * Scans for block comment text. This is any text except the block
   * comment start & end tokens, (* and *). This function will consume
   * everything up to (but not including) those tokens, until it hits
   * the end of the file. It is important that this function only returns
   * true if it has consumed at least 1 character, as otherwise the parser
   * enters an infinite loop. It is also important that the function not
   * consume the block comment start & end tokens themselves, which is why
   * this is in an external scanner rather than a regex in the grammar
   * itself.
   * 
   * For more info, see:
   * https://github.com/tlaplus-community/tree-sitter-tlaplus/issues/15
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @return Whether any block comment text was detected.
   **/
  bool scan_block_comment_text(TSLexer* const lexer) {
    lexer->result_symbol = BLOCK_COMMENT_TEXT;
    bool has_consumed_any = false;
    while (has_next(lexer)) {
      switch (next_codepoint(lexer)) {
        case '*': {
          lexer->mark_end(lexer);
          if (is_next_codepoint_sequence(lexer, BLOCK_COMMENT_END_TOKEN)) {
            return has_consumed_any;
          } else {
            has_consumed_any = true;
            break;
          }
        }
        case '(': {
          lexer->mark_end(lexer);
          if (is_next_codepoint_sequence(lexer, BLOCK_COMMENT_START_TOKEN)) {
            return has_consumed_any;
          } else {
            has_consumed_any = true;
            break;
          }
        }
        default:
          advance(lexer);
          has_consumed_any = true;
      }
    }

    lexer->mark_end(lexer);
    return has_consumed_any;
  }

  using column_index = int16_t;
  
  enum class JunctType {
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
    
    #define MARK_THEN_ADVANCE(state_value)            \
      {                                               \
        lexer->mark_end(lexer);                       \
        lexeme_start_col = lexer->get_column(lexer);  \
        ADVANCE(state_value);                         \
      }
    
    enum class LookaheadLexemeType {
      LAND,
      LOR,
      RIGHT_DELIMITER,
      COMMENT_START,
      TERMINATOR,
      OTHER
    };

    enum class LexState {
      CONSUME_LEADING_SPACE,
      FORWARD_SLASH,
      BACKWARD_SLASH,
      GT,
      EQ,
      DASH,
      LAND,
      LOR,
      L_PAREN,
      R_PAREN,
      R_SQUARE_BRACKET,
      R_CURLY_BRACE,
      R_ANGLE_BRACKET,
      RIGHT_ARROW,
      COMMENT_START,
      BLOCK_COMMENT_START,
      SINGLE_LINE,
      DOUBLE_LINE,
      A,
      ASSUM,
      ASSUME,
      ASSUMPTION,
      AX,
      AXIOM,
      C,
      CO,
      CON,
      COR,
      CONSTANT,
      CONSTANTS,
      COROLLARY,
      E,
      ELSE,
      I,
      IN,
      L,
      LE,
      LEMMA,
      LO,
      LOCAL,
      P,
      PROPOSITION,
      T,
      THE,
      THEN,
      THEOREM,
      V,
      VARIABLE,
      VARIABLES,
      OTHER
    };
    
    LookaheadLexemeType lex_lookahead_only_juncts(
      TSLexer* const lexer,
      column_index& lexeme_start_col
    ) {
      LexState state = LexState::CONSUME_LEADING_SPACE;
      START_LEXER();
      eof = !has_next(lexer);
      switch (state) {
        case LexState::CONSUME_LEADING_SPACE:
          if (eof) return LookaheadLexemeType::TERMINATOR;
          if ( ' '  == lookahead
            || 't'  == lookahead
            || '\r' == lookahead
            || '\n' == lookahead) SKIP(LexState::CONSUME_LEADING_SPACE);
          if ('/' == lookahead) MARK_THEN_ADVANCE(LexState::FORWARD_SLASH);
          if ('\\' == lookahead) MARK_THEN_ADVANCE(LexState::BACKWARD_SLASH);
          if (L'∧' == lookahead) MARK_THEN_ADVANCE(LexState::LAND);
          if (L'∨' == lookahead) MARK_THEN_ADVANCE(LexState::LOR);
          MARK_THEN_ADVANCE(LexState::OTHER);
        case LexState::FORWARD_SLASH:
          if ('\\' == lookahead) ADVANCE(LexState::LAND);
          return LookaheadLexemeType::OTHER;
        case LexState::BACKWARD_SLASH:
          if ('/' == lookahead) ADVANCE(LexState::LOR);
          return LookaheadLexemeType::OTHER;
        case LexState::LAND:
          return LookaheadLexemeType::LAND;
        case LexState::LOR:
          return LookaheadLexemeType::LOR;
        default:
          return LookaheadLexemeType::OTHER;
      }
    }

    LookaheadLexemeType lex_lookahead(
      TSLexer* const lexer,
      column_index& lexeme_start_col
    ) {
      LexState state = LexState::CONSUME_LEADING_SPACE;
      START_LEXER();
      eof = !has_next(lexer);
      switch (state) {
        case LexState::CONSUME_LEADING_SPACE:
          if (eof) return LookaheadLexemeType::TERMINATOR;
          if ( ' '  == lookahead
            || 't'  == lookahead
            || '\r' == lookahead
            || '\n' == lookahead) SKIP(LexState::CONSUME_LEADING_SPACE);
          if ('/' == lookahead) MARK_THEN_ADVANCE(LexState::FORWARD_SLASH);
          if ('\\' == lookahead) MARK_THEN_ADVANCE(LexState::BACKWARD_SLASH);
          if ('>' == lookahead) MARK_THEN_ADVANCE(LexState::GT);
          if ('=' == lookahead) MARK_THEN_ADVANCE(LexState::EQ);
          if ('-' == lookahead) MARK_THEN_ADVANCE(LexState::DASH);
          if ('(' == lookahead) MARK_THEN_ADVANCE(LexState::L_PAREN);
          if (')' == lookahead) MARK_THEN_ADVANCE(LexState::R_PAREN);
          if (']' == lookahead) MARK_THEN_ADVANCE(LexState::R_SQUARE_BRACKET);
          if ('}' == lookahead) MARK_THEN_ADVANCE(LexState::R_CURLY_BRACE);
          if ('A' == lookahead) MARK_THEN_ADVANCE(LexState::A);
          if ('C' == lookahead) MARK_THEN_ADVANCE(LexState::C);
          if ('E' == lookahead) MARK_THEN_ADVANCE(LexState::E);
          if ('I' == lookahead) MARK_THEN_ADVANCE(LexState::I);
          if ('L' == lookahead) MARK_THEN_ADVANCE(LexState::L);
          if ('P' == lookahead) MARK_THEN_ADVANCE(LexState::P);
          if ('T' == lookahead) MARK_THEN_ADVANCE(LexState::T);
          if ('V' == lookahead) MARK_THEN_ADVANCE(LexState::V);
          if (L'∧' == lookahead) MARK_THEN_ADVANCE(LexState::LAND);
          if (L'∨' == lookahead) MARK_THEN_ADVANCE(LexState::LOR);
          if (L'〉' == lookahead) MARK_THEN_ADVANCE(LexState::R_ANGLE_BRACKET);
          if (L'⟶' == lookahead) MARK_THEN_ADVANCE(LexState::RIGHT_ARROW);
          MARK_THEN_ADVANCE(LexState::OTHER);
        case LexState::FORWARD_SLASH:
          if ('\\' == lookahead) ADVANCE(LexState::LAND);
          return LookaheadLexemeType::OTHER;
        case LexState::BACKWARD_SLASH:
          if ('/' == lookahead) ADVANCE(LexState::LOR);
          if ('*' == lookahead) ADVANCE(LexState::COMMENT_START);
          return LookaheadLexemeType::OTHER;
        case LexState::GT:
          if ('>' == lookahead) ADVANCE(LexState::R_ANGLE_BRACKET);
          return LookaheadLexemeType::OTHER;
        case LexState::EQ:
          if (is_next_codepoint_sequence(lexer, {'=', '=', '='})) ADVANCE(LexState::DOUBLE_LINE);
          return LookaheadLexemeType::OTHER;
        case LexState::DASH:
          if ('>' == lookahead) ADVANCE(LexState::RIGHT_ARROW);
          if (is_next_codepoint_sequence(lexer, {'-', '-', '-'})) ADVANCE(LexState::SINGLE_LINE);
          return LookaheadLexemeType::OTHER;
        case LexState::LAND:
          return LookaheadLexemeType::LAND;
        case LexState::LOR:
          return LookaheadLexemeType::LOR;
        case LexState::L_PAREN:
          if ('*' == lookahead) ADVANCE(LexState::BLOCK_COMMENT_START);
          return LookaheadLexemeType::OTHER;
        case LexState::R_PAREN:
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::R_SQUARE_BRACKET:
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::R_CURLY_BRACE:
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::R_ANGLE_BRACKET:
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::RIGHT_ARROW:
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::COMMENT_START:
          return LookaheadLexemeType::COMMENT_START;
        case LexState::BLOCK_COMMENT_START:
          return LookaheadLexemeType::COMMENT_START;
        case LexState::SINGLE_LINE:
          return LookaheadLexemeType::TERMINATOR;
        case LexState::DOUBLE_LINE:
          return LookaheadLexemeType::TERMINATOR;
        case LexState::A:
          if ('X' == lookahead) ADVANCE(LexState::AX);
          if (is_next_codepoint_sequence(lexer, {'S','S','U','M'})) ADVANCE(LexState::ASSUM);
          return LookaheadLexemeType::OTHER;
        case LexState::ASSUM:
          if ('E' == lookahead) ADVANCE(LexState::ASSUME);
          if (is_next_codepoint_sequence(lexer, {'P','T','I','O','N'})) ADVANCE(LexState::ASSUMPTION);
          return LookaheadLexemeType::OTHER;
        case LexState::ASSUME:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::ASSUMPTION:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::AX:
          if (is_next_codepoint_sequence(lexer, {'I','O','M'})) ADVANCE(LexState::AXIOM);
          return LookaheadLexemeType::OTHER;
        case LexState::AXIOM:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::C:
          if ('O' == lookahead) ADVANCE(LexState::CO);
          return LookaheadLexemeType::OTHER;
        case LexState::CO:
          if ('N' == lookahead) ADVANCE(LexState::CON);
          if ('R' == lookahead) ADVANCE(LexState::COR);
          return LookaheadLexemeType::OTHER;
        case LexState::CON:
          if (is_next_codepoint_sequence(lexer, {'S','T','A','N','T'})) ADVANCE(LexState::CONSTANT);
          return LookaheadLexemeType::OTHER;
        case LexState::CONSTANT:
          if ('S' == lookahead) ADVANCE(LexState::CONSTANTS);
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::CONSTANTS:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::COR:
          if (is_next_codepoint_sequence(lexer, {'O','L','L','A','R','Y'})) ADVANCE(LexState::COROLLARY);
          return LookaheadLexemeType::OTHER;
        case LexState::E:
          if (is_next_codepoint_sequence(lexer, {'L','S','E'})) ADVANCE(LexState::ELSE);
          return LookaheadLexemeType::OTHER;
        case LexState::ELSE:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::I:
          if ('N' == lookahead) ADVANCE(LexState::IN);
          return LookaheadLexemeType::OTHER;
        case LexState::IN:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::L:
          if ('E' == lookahead) ADVANCE(LexState::LE);
          if ('O' == lookahead) ADVANCE(LexState::LO);
          return LookaheadLexemeType::OTHER;
        case LexState::LE:
          if (is_next_codepoint_sequence(lexer, {'M','M','A'})) ADVANCE(LexState::LEMMA);
          return LookaheadLexemeType::OTHER;
        case LexState::LEMMA:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::LO:
          if (is_next_codepoint_sequence(lexer, {'C','A','L'})) ADVANCE(LexState::LOCAL);
          return LookaheadLexemeType::OTHER;
        case LexState::LOCAL:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::P:
          if (is_next_codepoint_sequence(lexer, {'R','O','P','O','S','I','T','I','O','N'})) ADVANCE(LexState::PROPOSITION);
          return LookaheadLexemeType::OTHER;
        case LexState::PROPOSITION:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::T:
          if (is_next_codepoint_sequence(lexer, {'H','E'})) ADVANCE(LexState::THE);
          return LookaheadLexemeType::OTHER;
        case LexState::THE:
          if ('N' == lookahead) ADVANCE(LexState::THEN);
          if (is_next_codepoint_sequence(lexer, {'O','R','E','M'})) ADVANCE(LexState::THEOREM);
          return LookaheadLexemeType::OTHER;
        case LexState::THEN:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::RIGHT_DELIMITER;
        case LexState::THEOREM:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::V:
          if (is_next_codepoint_sequence(lexer, {'A','R','I','A','B','L','E'})) ADVANCE(LexState::VARIABLE);
          return LookaheadLexemeType::OTHER;
        case LexState::VARIABLE:
          if ('S' == lookahead) ADVANCE(LexState::VARIABLES);
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::VARIABLES:
          if (is_identifier_char(lookahead)) return LookaheadLexemeType::OTHER;
          return LookaheadLexemeType::TERMINATOR;
        case LexState::OTHER:
          return LookaheadLexemeType::OTHER;
        default:
          return LookaheadLexemeType::OTHER;
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
      // Tree-sitter calls the scanner with every symbol marked valid
      // when it enters error recovery mode.
      const bool is_error_recovery =
        valid_symbols[EXTRAMODULAR_TEXT]
        && valid_symbols[BLOCK_COMMENT_TEXT]
        && valid_symbols[INDENT]
        && valid_symbols[NEWLINE]
        && valid_symbols[DEDENT];

      // TODO: actually function during error recovery
      // https://github.com/tlaplus-community/tree-sitter-tlaplus/issues/19
      if (is_error_recovery) {
        return false;
      } else if(valid_symbols[EXTRAMODULAR_TEXT]) {
        return scan_extramodular_text(lexer);
      } else if (valid_symbols[BLOCK_COMMENT_TEXT]) {
        return scan_block_comment_text(lexer);
      } else if (valid_symbols[INDENT]
        || valid_symbols[NEWLINE]
        || valid_symbols[DEDENT]
      ) {
        column_index col;
        if (!is_in_jlist()) {
          switch(lex_lookahead_only_juncts(lexer, col)) {
            case LookaheadLexemeType::LAND:
              return handle_junct_token(lexer, valid_symbols, JunctType::CONJUNCTION, col);
            case LookaheadLexemeType::LOR:
              return handle_junct_token(lexer, valid_symbols, JunctType::DISJUNCTION, col);
            default:
              return false;
          }
        } else {
          switch (lex_lookahead(lexer, col)) {
            case LookaheadLexemeType::LAND:
              return handle_junct_token(lexer, valid_symbols, JunctType::CONJUNCTION, col);
            case LookaheadLexemeType::LOR:
              return handle_junct_token(lexer, valid_symbols, JunctType::DISJUNCTION, col);
            case LookaheadLexemeType::RIGHT_DELIMITER:
              return handle_right_delimiter_token(lexer, valid_symbols, col);
            case LookaheadLexemeType::COMMENT_START:
              return false;
            case LookaheadLexemeType::TERMINATOR:
              return handle_terminator_token(lexer, valid_symbols);
            case LookaheadLexemeType::OTHER:
              return handle_other_token(lexer, valid_symbols, col);
            default:
              return false;
          }
        }
      } else {
        return false;
      }
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
