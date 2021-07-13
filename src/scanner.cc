#include <tree_sitter/parser.h>
#include <cassert>
#include <vector>
#include <set>
#include <cstring>
#include <functional>

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
  static const token_t LAND_TOKEN = {'/','\\'};
  static const token_t UNICODE_LAND_TOKEN = {L'∧'};
  static const token_t LOR_TOKEN = {'\\','/'};
  static const token_t UNICODE_LOR_TOKEN = {L'∨'};
  static const token_t R_PARENTHESIS_TOKEN = {')'};
  static const token_t R_SQUARE_BRACKET_TOKEN = {']'};
  static const token_t R_CURLY_BRACE_TOKEN = {'}'};
  static const token_t R_ANGLE_BRACKET_TOKEN = {'>','>'};
  static const token_t UNICODE_R_ANGLE_BRACKET_TOKEN = {L'〉'};
  static const token_t CASE_ARROW_TOKEN = {'-','>'};
  static const token_t UNICODE_CASE_ARROW_TOKEN = {L'⟶'};
  static const token_t COMMENT_START_TOKEN = {'\\','*'};
  static const token_t BLOCK_COMMENT_START_TOKEN = {'(','*'};
  static const token_t BLOCK_COMMENT_END_TOKEN = {'*',')'};
  static const token_t SINGLE_LINE_TOKEN = {'-','-','-','-'};
  static const token_t MODULE_END_TOKEN = {'=','=','=','='};
  static const token_t ASSUME_TOKEN = {'A','S','S','U','M','E'};
  static const token_t ASSUMPTION_TOKEN = {'A','S','S','U','M','P','T','I','O','N'};
  static const token_t AXIOM_TOKEN = {'A','X','I','O','M'};
  static const token_t CONSTANT_TOKEN = {'C','O','N','S','T','A','N','T'};
  static const token_t CONSTANTS_TOKEN = {'C','O','N','S','T','A','N','T','S'};
  static const token_t COROLLARY_TOKEN = {'C','O','R','O','L','L','A','R','Y'};
  static const token_t ELSE_TOKEN = {'E','L','S','E'};
  static const token_t IN_TOKEN = {'I','N'};
  static const token_t INSTANCE_TOKEN = {'I','N','S','T','A','N','C','E'};
  static const token_t LEMMA_TOKEN = {'L','E','M','M','A'};
  static const token_t LOCAL_TOKEN = {'L','O','C','A','L'};
  static const token_t MODULE_TOKEN = {'M','O','D','U','L','E'};
  static const token_t PROPOSITION_TOKEN = {'P','R','O','P','O','S','I','T','I','O','N'};
  static const token_t RECURSIVE_TOKEN = {'R','E','C','U','R','S','I','V','E'};
  static const token_t THEN_TOKEN = {'T','H','E','N'};
  static const token_t THEOREM_TOKEN = {'T','H','E','O','R','E','M'};
  static const token_t VARIABLE_TOKEN = {'V','A','R','I','A','B','L','E'};
  static const token_t VARIABLES_TOKEN = {'V','A','R','I','A','B','L','E','S'};

  /**
   * Interesting token types for the purpose of parsing junctlists.
   */
  enum LookaheadTokenType {
    LAND,             // /\ or ∧
    LOR,              // \/ or ∨
    RIGHT_DELIMITER,  // ), ], }, 〉, or >>
    COMMENT,          // \*, (*, *)
    UNIT,             // op == expr, etc.
    MODULE_END,       // ====
    END_OF_FILE,      // The end of the file.
    OTHER             // Tokens not requiring special handling logic.
  };

  /**
   * A type for representing association between tokens and their category.
   */
  struct TokenTypeMap {
    const token_t& token;
    LookaheadTokenType type;
    TokenTypeMap(const token_t& tk, LookaheadTokenType tp)
      : token(tk), type(tp) {}
  };

  // The actual mapping between tokens and their type/category.
  static const std::vector<TokenTypeMap> LOOKAHEAD_TOKEN_TYPE_MAPPING = {
    TokenTypeMap(LAND_TOKEN, LAND),
    TokenTypeMap(UNICODE_LAND_TOKEN, LAND),
    TokenTypeMap(LOR_TOKEN, LOR),
    TokenTypeMap(UNICODE_LOR_TOKEN, LOR),
    TokenTypeMap(R_PARENTHESIS_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(R_SQUARE_BRACKET_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(R_CURLY_BRACE_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(R_ANGLE_BRACKET_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(UNICODE_R_ANGLE_BRACKET_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(CASE_ARROW_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(UNICODE_CASE_ARROW_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(COMMENT_START_TOKEN, COMMENT),
    TokenTypeMap(BLOCK_COMMENT_START_TOKEN, COMMENT),
    TokenTypeMap(SINGLE_LINE_TOKEN, UNIT),
    TokenTypeMap(MODULE_END_TOKEN, MODULE_END),
    TokenTypeMap(ASSUME_TOKEN, UNIT),
    TokenTypeMap(ASSUMPTION_TOKEN, UNIT),
    TokenTypeMap(AXIOM_TOKEN, UNIT),
    TokenTypeMap(CONSTANT_TOKEN, UNIT),
    TokenTypeMap(CONSTANTS_TOKEN, UNIT),
    TokenTypeMap(COROLLARY_TOKEN, UNIT),
    TokenTypeMap(ELSE_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(IN_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(INSTANCE_TOKEN, UNIT),
    TokenTypeMap(LEMMA_TOKEN, UNIT),
    TokenTypeMap(LOCAL_TOKEN, UNIT),
    TokenTypeMap(PROPOSITION_TOKEN, UNIT),
    TokenTypeMap(RECURSIVE_TOKEN, UNIT),
    TokenTypeMap(THEN_TOKEN, RIGHT_DELIMITER),
    TokenTypeMap(THEOREM_TOKEN, UNIT),
    TokenTypeMap(VARIABLE_TOKEN, UNIT),
    TokenTypeMap(VARIABLES_TOKEN, UNIT)
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
   * Consumes codepoints as long as the given condition function returns
   * true, or lexer hits EOF.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param is_whitespace Whether to mark consumed as whitespace.
   * @param condition Function determining whether to continue consuming.
   * @return Number of codepoints consumed.
   **/
  size_t consume_while(
    TSLexer* const lexer,
    const bool is_whitespace,
    const std::function<bool(int32_t)>& condition
  ) {
    size_t consume_count = 0;
    while (has_next(lexer) && condition(next_codepoint(lexer))) {
      lexer->advance(lexer, is_whitespace);
      consume_count++;
    }

    return consume_count;
  }

  /**
   * Checks whether the next token is the one given.
   * A token is a sequence of codepoints.
   * This function can change the state of the lexer.
   * Keeps track of number of consumed codepoints.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param token The token to check for.
   * @param out_consumed_count Out parameter; number of codepoints consumed.
   * @return Whether the next token is the one given.
   */
  bool is_next_token(
    TSLexer* const lexer,
    const token_t& token,
    size_t& out_consumed_count
  ) {
    for (int32_t codepoint : token) {
      if (!is_next_codepoint(lexer, codepoint)) {
        return false;
      }

      advance(lexer);
      out_consumed_count++;
    }

    return true;
  }

  /**
   * Checks whether the next token is the one given.
   * A token is a sequence of codepoints.
   * This function can change the state of the lexer.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param token The token to check for.
   * @return Whether the next token is the one given.
   */
  bool is_next_token(TSLexer* const lexer, const token_t& token) {
    size_t consumed;
    return is_next_token(lexer, token, consumed);
  }

  /**
   * Looks ahead at a list of tokens to see whether any match.
   * Given multiple matches, returns type of longest.
   * Works best with small (fewer than 100) number of possible tokens, as
   * for simplicity complexity is |tokens| * max({|t| : t \in tokens}).
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param tokens The list of tokens to check for, with types.
   * @return Type of token matched, or Other if none matched.
   **/
  LookaheadTokenType token_lookahead(
    TSLexer* const lexer,
    const std::vector<TokenTypeMap>& tokens
  ) {
    bool any_undecided = true;
    std::vector<bool> decided(tokens.size());
    std::vector<int> matches;
    for (
      size_t lookahead = 0;
      any_undecided && has_next(lexer);
      lookahead++, advance(lexer)
    ) {
      any_undecided = false;
      for (int i = 0; i < tokens.size(); i++) {
        if (!decided.at(i)) {
          const token_t& token = tokens.at(i).token;
          if (is_next_codepoint(lexer, token.at(lookahead))) {
            if (lookahead + 1 == token.size()) {
              decided[i] = true;
              matches.push_back(i);
            } else {
              any_undecided = true;
            }
          } else {
            // Not a match
            decided[i] = true;
          }
        }
      }
    }

    // Pick longest match
    size_t longest_match_length = 0;
    LookaheadTokenType longest_match_type = OTHER;
    for (int match : matches) {
      if (tokens.at(match).token.size() > longest_match_length) {
        longest_match_type = tokens.at(match).type;
      }
    }

    return longest_match_type;
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
    consume_while(lexer, true, is_whitespace);
    bool has_consumed_any = false;
    while (has_next(lexer)) {
      if (is_next_codepoint(lexer, '-')) {
        lexer->mark_end(lexer);
        if (is_next_token(lexer, SINGLE_LINE_TOKEN)) {
          consume_while(lexer, false, [](int32_t cp) {return '-' == cp;});
          consume_while(lexer, false, [](int32_t cp) {return ' ' == cp;});
          if (is_next_token(lexer, MODULE_TOKEN)) {
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
          if (is_next_token(lexer, BLOCK_COMMENT_END_TOKEN)) {
            return has_consumed_any;
          } else {
            has_consumed_any = true;
            break;
          }
        }
        case '(': {
          lexer->mark_end(lexer);
          if (is_next_token(lexer, BLOCK_COMMENT_START_TOKEN)) {
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

  /**
   * Scans for & identifies the next token relevant to junctlists.
   * 
   * @param lexer The tree-sitter lexing control structure.
   * @param out_col Out parameter; the column of the identified token.
   * @return The type of token identified.
   */
  LookaheadTokenType get_next_token(
    TSLexer* const lexer,
    column_index& out_col
  ) {
    consume_while(lexer, true, is_whitespace);
    lexer->mark_end(lexer);
    out_col = lexer->get_column(lexer);
    return
      !has_next(lexer)
      ? END_OF_FILE
      : token_lookahead(lexer, LOOKAHEAD_TOKEN_TYPE_MAPPING);
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
        switch (get_next_token(lexer, col)) {
          case LAND:
            return handle_junct_token(lexer, valid_symbols, CONJUNCTION, col);
          case LOR:
            return handle_junct_token(lexer, valid_symbols, DISJUNCTION, col);
          case RIGHT_DELIMITER:
            return handle_right_delimiter_token(lexer, valid_symbols, col);
          case COMMENT:
            return false;
          case UNIT:
            return handle_terminator_token(lexer, valid_symbols);
          case MODULE_END:
            return handle_terminator_token(lexer, valid_symbols);
          case END_OF_FILE:
            return handle_terminator_token(lexer, valid_symbols);
          case OTHER:
            return handle_other_token(lexer, valid_symbols, col);
          default:
            return false;
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
