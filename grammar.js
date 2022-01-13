// A sequence of one or more comma-separated strings matching the rule
function commaList1(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

// A sequence of zero or more comma-separated strings matching the rule
function commaList(rule) {
  return optional(commaList1(rule))
}

// An operator with one parameter.
function arity1(op, expr) {
  return seq(op, '(', expr, ')')
}

// An operator with two parameters.
function arity2(op, expr) {
  return seq(op, '(', expr, ',', expr, ')')
}

// An operator with 0 or more parameters.
function arity0OrN(op, expr) {
  return seq(
    field('name', op),
    field('parameter', optional(seq('(', commaList1(expr), ')'))))
}

// An operator with 1 or more parameters.
function arity1OrN(op, expr) {
  return seq(
    field('name', op),
    seq('(', commaList1(expr), ')')
  )
}

// A rule matching either the first or second rule, or the first then the
// second rule, but not matching nothing.
function oneOrBoth(first, second) {
  return choice(first, second, seq(first, second))
}

// Defines a labelled left-associative prefix operator of given precedence
function prefixOpPrec(level, expr, symbol) {
  return prec.left(level, seq(
    field('symbol', symbol),
    field('rhs', expr)
  ))
}

// Defines a labelled left-associative infix operator of given precedence
function infixOpPrec(level, expr, symbol) {
  return prec.left(level, seq(
    field('lhs', expr),
    field('symbol', symbol),
    field('rhs', expr)
  ))
}

// Defines a labelled postfix operator of given precedence
function postfixOpPrec(level, expr, symbol) {
  return prec(level, seq(
    field('lhs', expr),
    field('symbol', symbol)
  ))
}

function regexOr(regex) {
    if (arguments.length > 1) {
        regex = Array.from(arguments).join('|');
    }
    return {
        type: 'PATTERN',
        value: regex
    };
}

module.exports = grammar({
  name: 'tlaplus',

  externals: $ => [
    $.extramodular_text,
    $._indent,
    $.bullet_conj,
    $.bullet_disj,
    $._dedent,
    $._begin_proof,
    $._begin_proof_step,
    $.proof_keyword,
    $.by_keyword,
    $.obvious_keyword,
    $.omitted_keyword,
    $.qed_keyword,
    $._error_sentinel
  ],
  
  word: $ => $.identifier,

  supertypes: $ => [
    $._unit,
    $._expr,
    $._op,
    $._proof,
    $._number,
    $._primitive_value_set
  ],

  extras: $ => [
    /\s|\r?\n/,
    $.comment,
    $.block_comment,
  ],
  
  // Prefix, infix, and postfix operator precedence categories, defined
  // on p271 of Specifying Systems. Precedences defined in this way are
  // defined only in relation to each other, not to every other rule.
  // See https://github.com/tree-sitter/tree-sitter/pull/939
  precedences: $ => [
    [
      '17-17',  '16-16',  '15-15',  '14-14',  '13-13',  '12-12',  '11-11',
      '10-10',  '9-9',    '8-8',    '7-7',    '6-6',    '5-5',    '4-4',
      '3-3',    '2-2',    '1-1',    '0-0'
    ],
  ],

  conflicts: $ => [
    // Lookahead to disambiguate '-'  •  '('  …
    [$.minus, $.negative],
    // Lookahead to disambiguate lnot • '('  …
    // Could be nonfix prefix op or prefix op applied to expr in parentheses.
    [$.bound_prefix_op, $.prefix_op_symbol],
    // Lookahead to disambiguate 'SF_'  identifier  •  '('  …
    // Could be SF_op(x)(e) or could be SF_id(e)
    [$.bound_op, $._subscript_expr],
    // Lookahead to disambiguate SF_'  subexpr_prefix  identifier  •  '('  …
    // Could be SF_A!B!C!op(x)(e) or could be SF_A!B!C!id(e)
    [$.bound_op, $.prefixed_op],
    // Lookahead to disambiguate identifier '(' identifier •  ',' …
    // Could be op(a, b) or could be lbl(a, b) ::
    [$._expr, $.label],
    // Lookahead to disambiguate '['  identifier  •  '\in'  …
    // Matches both step_expr_or_stutter and function_literal
    [$._expr, $.quantifier_bound],
    // Lookahead to disambiguate '{'  identifier  •  '\in'  …
    // Matches set_filter, set_map, and finite_set_literal
    [$._expr, $.single_quantifier_bound],
    // Lookahead to disambiguate '['  langle_bracket  identifier  •  '>>'  …
    // Matches step_expr_or_stutter and function_literal
    [$._expr, $.tuple_of_identifiers],
    // Lookahead to disambiguate identifier  •  '\in'  …
    // Could be x \in y == ... (op def'n) or x \in S (expression)
    [$._expr, $.operator_definition],
    // Lookahead to disambiguate identifier  '('  identifier  •  ','  …
    // Could be op(a, b) == ... (decl'n) or op(a, b) (expression) or label
    [$._expr, $._id_or_op_declaration, $.label],
    // Lookahead to disambiguate identifier  •  '['  …
    // Could be f[x \in S] == ... (function def'n) or f[x] (application)
    [$._expr, $.function_definition],
    // Lookahead to disambiguate subexpr_component  '!'  •  '\in'  …
    // The '\in' could be followed by a ! or it could be the end
    [$.subexpr_prefix],
    // Lookahead to disambiguate identifier  •  '['  …
    // Could be application `f[x]` or could be assignment `record[x] :=`
    [$._expr, $.pcal_lhs],
    // Lookahead to disambiguate _expr  •  '||'  …
    // Could be `x || y` or could be assignment `x := y || y := x`
    [$.bound_infix_op, $.pcal_assign],
  ],

  rules: {
    source_file: $ => seq(
      repeat1(seq(optional($.extramodular_text), $.module)),
      optional($.extramodular_text)
    ),

    // \* this is a comment ending with newline
    comment: $ => /\\\*.*/,

    // source: https://github.com/tree-sitter/tree-sitter/discussions/1252#discussioncomment-988725
    block_comment: $ => seq(
      '(*',
      repeat(
        choice($.pcal_algorithm, 
               $.block_comment_text)
      ),
      '*)'
    ),

    block_comment_text: $ => 
      prec.right(repeat1(
        choice(
          regexOr(
            '[^*()\n]', // any symbol except reserved
            '[^*\n][)]', // closing parenthesis, which is not a comment end
            '[(][^(*\n]', // opening parenthesis, which is not a comment start
            '[)][*][^)\n]',
            '[*][^*)\n]',
            '[*][)][ \t]*[\n]?[ \t]*[(][*]' // contiguous block comment border
          ),
          /\*/,
          /\(/,
          /\)/,
        )
      )),

    // Top-level module declaration
    module: $ => seq(
      alias($.single_line, $.header_line),
      'MODULE', field('name', $.identifier),
      alias($.single_line, $.header_line),
      optional($.extends),
      repeat($._unit),
      $.double_line
    ),

    // Line of ---------- of length at least 4
    single_line: $ => /-----*/,

    // Line of =========== of length at least 4
    double_line: $ => /=====*/,

    // Various syntactic elements and their unicode equivalents
    def_eq:             $ => choice('==', '≜'),
    set_in:             $ => choice('\\in', '∈'),
    gets:               $ => choice('<-', '⟵', '←'),
    forall:             $ => choice('\\A', '\\forall', '∀'),
    exists:             $ => choice('\\E', '\\exists', '∃'),
    temporal_forall:    $ => choice('\\AA'),
    temporal_exists:    $ => choice('\\EE'),
    all_map_to:         $ => choice('|->', '⟼', '↦'), 
    maps_to:            $ => choice('->', '⟶', '→'),
    langle_bracket:     $ => choice('<<', '〈', '⟨'),
    rangle_bracket:     $ => choice('>>', '〉', '⟩'),
    rangle_bracket_sub: $ => choice('>>_', '〉_', '⟩_'),
    case_box:           $ => choice('[]', '□'),
    case_arrow:         $ => choice('->', '⟶', '→'),
    colon:              $ => ':',
    address:            $ => '@',
    label_as:           $ => choice('::', '∷'),
    placeholder:        $ => '_',

    // The set of all reserved keywords
    keyword: $ => choice(
      'ASSUME',       'ELSE',       'LOCAL',      'UNION',
      'ASSUMPTION',   'ENABLED',    'MODULE',     'VARIABLE',
      'AXIOM',        'EXCEPT',     'OTHER',      'VARIABLES',
      'CASE',         'EXTENDS',    'SF_',        'WF_',
      'CHOOSE',       'IF',         'SUBSET',     'WITH',
      'CONSTANT',     'IN',         'THEN',
      'CONSTANTS',    'INSTANCE',   'THEOREM',    'COROLLARY',
      'DOMAIN',       'LET',        'UNCHANGED',
      'BY',           'HAVE',       'QED',        'TAKE',
      'DEF',          'HIDE',       'RECURSIVE',  'USE',
      'DEFINE',       'PROOF',      'WITNESS',    'PICK',
      'DEFS',         'PROVE',      'SUFFICES',   'NEW',
      'LAMBDA',       'STATE',      'ACTION',     'TEMPORAL',
      'OBVIOUS',      'OMITTED',    'LEMMA',      'PROPOSITION',
      'ONLY'
    ),

    // General-purpose identifier, should exclude reserved keywords,
    // but tree-sitter currently does not support match exclusion logic.
    // https://github.com/tlaplus-community/tree-sitter-tlaplus/issues/14
    // Can contain letters, numbers, and underscores
    // If only one character long, must be letter (not number or _)
    identifier: $ => /\w*[A-Za-z]\w*/,

    // EXTENDS Naturals, FiniteSets, Sequences
    extends: $ => seq(
      'EXTENDS', commaList1(alias($.identifier, $.identifier_ref))
    ),

    // A module-level definition
    _unit: $ => choice(
      $.variable_declaration,
      $.constant_declaration,
      $.recursive_declaration,
      $.use_or_hide,
      $.local_definition,
      $._definition,
      $.assumption,
      $.theorem,
      $.module,
      $.single_line
    ),
    
    local_definition: $ => seq('LOCAL', $._definition),

    _definition: $ => choice(
      $.operator_definition,
      $.function_definition,
      $.instance,
      $.module_definition,
    ),

    // VARIABLES v1, v2, v3
    variable_declaration: $ => seq(
        choice('VARIABLE', 'VARIABLES'),
        commaList1($.identifier)
    ),

    // CONSTANTS C1, C2, C3
    constant_declaration: $ => seq(
        choice('CONSTANT', 'CONSTANTS'),
        commaList1($._id_or_op_declaration)
    ),

    // RECURSIVE op(_, _)
    recursive_declaration: $ => seq(
      'RECURSIVE', commaList1($._id_or_op_declaration)
    ),

    // Operator declaration (not definition)
    // Used, for example, when op accepts another op as parameter
    // op, op(_,_), _+_, etc.
    operator_declaration: $ => choice(
      arity1OrN($.identifier, $.placeholder),
      seq(field('name', $.prefix_op_symbol), $.placeholder),
      seq($.placeholder, field('name', $.infix_op_symbol), $.placeholder),
      seq($.placeholder, field('name', $.postfix_op_symbol))
    ),

    // Either an identifier or an operator declaration
    // Used to define parameters to operators during their definition
    _id_or_op_declaration: $ => choice(
      $.identifier,
      $.operator_declaration
    ),

    // Operator definition
    // max(a, b) == IF a > b THEN a ELSE b
    // a \prec b == a.val < b.val
    // x ≜ 〈 1, 2, 3, 4, 5 〉
    operator_definition: $ => seq(
      choice(
        arity0OrN($.identifier, $._id_or_op_declaration),
        seq(
          field('name', $.prefix_op_symbol),
          field('parameter', $.identifier)
        ),
        seq(
          field('parameter', $.identifier),
          field('name', $.infix_op_symbol),
          field('parameter', $.identifier)
        ),
        seq(
          field('parameter', $.identifier),
          field('name', $.postfix_op_symbol)
        )
      ),
      $.def_eq,
      field('definition', $._expr)
    ),

    // f[x \in Nat] == 2*x
    function_definition: $ => seq(
      field('name', $.identifier),
      '[', commaList1($.quantifier_bound), ']',
      $.def_eq,
      field('definition', $._expr)
    ),

    // x, y, z \in S
    // <<x, y, z>> \in S \X T \X P
    quantifier_bound: $ => seq(
      choice(
        commaList1($.identifier),
        $.tuple_of_identifiers
      ),
      $.set_in,
      field('set', $._expr)
    ),

    // x \in S
    // <<x, y, z>> \in S \X T \X P
    single_quantifier_bound: $ => seq(
      choice(
        $.identifier,
        $.tuple_of_identifiers
      ),
      $.set_in,
      $._expr
    ),

    // <<x, y, z>>
    tuple_of_identifiers: $ => seq(
      $.langle_bracket,
      commaList1($.identifier),
      $.rangle_bracket
    ),

    // INSTANCE ModuleName WITH x <- y, w <- z
    instance: $ => seq(
      'INSTANCE',
      alias($.identifier, $.identifier_ref),
      optional(seq('WITH', commaList1($.substitution)))
    ),

    // x <- y, w <- z
    substitution: $ => seq(
      choice(
        alias($.identifier, $.identifier_ref),
        $.prefix_op_symbol,
        $.infix_op_symbol,
        $.postfix_op_symbol
      ),
      $.gets,
      $._op_or_expr
    ),

    // Either an operator (op, +, *, LAMBDA, etc.) or an expression
    _op_or_expr: $ => choice($._op, $._expr),

    _op: $ => choice(
      $.prefix_op_symbol,
      $.infix_op_symbol,
      $.postfix_op_symbol,
      $.lambda,
    ),

    // foo!bar!baz!
    subexpr_prefix: $ => seq(
      choice($.subexpr_component, $.proof_step_ref), '!',
      repeat(seq(choice($.subexpr_component, $.subexpr_tree_nav), '!'))
    ),

    // Subexpression component referencing a previously-defined symbol
    // Can either bind parameters to the op or leave them unbound
    subexpr_component: $ => choice(
      alias($.identifier, $.identifier_ref),
      $.bound_op,
      $.bound_nonfix_op,
      $.prefix_op_symbol,
      $.infix_op_symbol,
      $.postfix_op_symbol
    ),

    // f(a, op, b)
    bound_op: $ => arity1OrN(alias($.identifier, $.identifier_ref), $._op_or_expr),

    // +(2, 4)
    bound_nonfix_op: $ => choice(
      arity1($.prefix_op_symbol, $._expr),
      arity2($.infix_op_symbol, $._expr),
      arity1($.postfix_op_symbol, $._expr)
    ),

    // Metalanguage to navigate the parse tree of an expression
    // F!:!〈!〉!2!(0, 3)!@
    subexpr_tree_nav: $ => choice(
      $.langle_bracket,   // first parse node child
      $.rangle_bracket,   // second parse node child
      $.child_id,         // nth parse node child
      $.colon,            // for recursive operators
      $.address,          // use unbound quantifier as lambda
      $.operator_args     // bind quantifier
    ),

    // ...!2!3!...
    child_id: $ => /\d+/,

    // ...!(a, b, c)!...
    operator_args: $ => seq(
      '(', commaList1($._op_or_expr), ')'
    ),

    // LAMBDA a, b, c : a + b * c
    lambda: $ => seq(
      'LAMBDA', commaList1($.identifier), ':', $._expr
    ),

    // M == INSTANCE ModuleName
    module_definition: $ => seq(
      arity0OrN($.identifier, $._id_or_op_declaration),
      $.def_eq,
      field('definition', $.instance)
    ),

    /************************************************************************/
    /* EXPRESSIONS                                                          */
    /************************************************************************/

    // Anything that evaluates to a value
    _expr: $ => choice(
      $._number,
      $.string,
      $.boolean,
      $._primitive_value_set,
      $.parentheses,
      $.label,
      $.subexpression,
      $.proof_step_ref,
      alias($.identifier, $.identifier_ref),
      $.bound_op,
      $.bound_nonfix_op,
      $.prefixed_op,
      $.bound_prefix_op,
      $.bound_infix_op,
      $.bound_postfix_op,
      $.bounded_quantification,
      $.unbounded_quantification,
      $.choose,
      $.finite_set_literal,
      $.set_filter,
      $.set_map,
      $.function_evaluation,
      $.function_literal,
      $.set_of_functions,
      $.record_literal,
      $.set_of_records,
      $.record_value,
      $.except,
      $.prev_func_val,
      $.tuple_literal,
      $.step_expr_or_stutter,
      $.step_expr_no_stutter,
      $.fairness,
      $.if_then_else,
      $.case,
      $.let_in,
      $.conj_list,
      $.disj_list,
    ),

    // Expressions allowed in subscripts; must be enclosed in delimiters
    // Used in WF_expr, <><<f>>_expr, etc.
    _subscript_expr: $ => choice(
      alias($.identifier, $.identifier_ref),
      $.bound_op,
      $.bound_nonfix_op,
      $.prefixed_op,
      $.parentheses,
      $.finite_set_literal,
      $.set_filter,
      $.set_map,
      $.function_literal,
      $.set_of_functions,
      $.record_literal,
      $.set_of_records,
      $.except,
      $.tuple_literal,
      $.step_expr_or_stutter,
      $.step_expr_no_stutter,
    ),

    // foo!bar!baz!op(x, y)
    prefixed_op: $ => seq(
      field('prefix', $.subexpr_prefix),
      field('op', choice(
        alias($.identifier, $.identifier_ref),
        $.bound_op,
        $.bound_nonfix_op
      ))
    ),

    // Number literal encodings
    _number: $ => choice(
      $.nat_number,     $.real_number,
      $.binary_number,  $.octal_number,   $.hex_number
    ),

    // 12345
    nat_number: $ => /\d+/,

    // 3.14159
    real_number: $ => /\d*\.\d+/,

    // \B01010101
    binary_number: $ => seq(
      alias(choice('\\b', '\\B'), $.format),
      alias(token.immediate(/[0-1]+/), $.value)
    ),

    // \O01234567
    octal_number: $ => seq(
      alias(choice('\\o', '\\O'), $.format),
      alias(token.immediate(/[0-7]+/), $.value)
    ),

    // \HDEADC0DE
    hex_number: $ => seq(
      alias(choice('\\h', '\\H'), $.format),
      alias(token.immediate(/[0-9a-fA-F]+/), $.value)
    ),

    // "foobar", "", etc.
    string: $ => seq(
      '"',
      repeat(choice(
        token.immediate(/[^"\n]/),
        $.escape_char
      )),
      token.immediate('"')
    ),

    // "/\\", "say \"hello\" back", "one\ntwo"
    escape_char: $ => seq(
      token.immediate('\\'),
      token.immediate(/./)
    ),

    // TRUE, FALSE, BOOLEAN
    boolean: $ => choice('TRUE', 'FALSE'),

    // Set of all strings, booleans, and numbers
    _primitive_value_set: $ => choice(
      $.string_set,     $.boolean_set,  $.nat_number_set,
      $.int_number_set, $.real_number_set
    ),
    string_set:       $ => 'STRING',            // From TLA+ builtins
    boolean_set:      $ => 'BOOLEAN',           // From TLA+ builtins
    nat_number_set:   $ => choice('Nat', 'ℕ'),  // From Naturals standard module
    int_number_set:   $ => choice('Int', 'ℤ'),  // From Integers standard module
    real_number_set:  $ => choice('Real', 'ℝ'), // From Reals standard module

    // Label for less-fragile addressing of subexpressions
    // lbl(a, b) :: e
    label: $ => prec('0-0', seq(
      arity0OrN($.identifier, $.identifier),
      $.label_as,
      $._expr
    )),

    // Address subexpressions through syntax tree navigation
    // op!+!<<!@
    subexpression: $ => seq(
      $.subexpr_prefix,
      $.subexpr_tree_nav
    ),

    // ((a + b) + c)
    parentheses: $ => seq('(', $._expr, ')'),

    // \A x \in Nat : P(x)
    bounded_quantification: $ => prec('0-0', seq(
      field('quantifier', choice($.forall, $.exists)),
      field('bound', commaList1($.quantifier_bound)),
      ':',
      field('expression', $._expr)
    )),

    // \EE x : P(x)
    unbounded_quantification: $ => prec('0-0', seq(
      field('quantifier', choice(
        $.forall, $.exists, $.temporal_forall, $.temporal_exists
      )),
      field('identifier', commaList1($.identifier)),
      ':',
      field('expression', $._expr)
    )),

    // CHOOSE r \in Real : r >= 0
    choose: $ => prec('0-0', seq(
      'CHOOSE',
      choice($.identifier, $.tuple_of_identifiers),
      optional(seq($.set_in, $._expr)),
      ':',
      $._expr
    )),

    // {1, 2, 3, 4, 5}
    finite_set_literal: $ => seq('{', commaList($._expr), '}'),

    // { x \in S : P(x) }
    // Set dynamic precedence to 1 so that the expression {x \in S : x \in P}
    // is parsed as set_filter instead of set_map during GLR parsing.
    set_filter: $ => prec.dynamic(1, seq(
      '{',
      field('generator', $.single_quantifier_bound),
      ':',
      field('filter', $._expr),
      '}'
    )),

    // { f[x, y] : x, y \in S }
    set_map: $ => seq(
      '{',
      field('map', $._expr),
      ':',
      field('generator', commaList1($.quantifier_bound)),
      '}'
    ),

    // f[5]
    function_evaluation: $ => prec('16-16', seq(
      $._expr, '[', commaList1($._expr), ']'
    )),

    // [n \in Nat |-> 2*n]
    function_literal: $ => seq(
      '[', commaList1($.quantifier_bound), $.all_map_to, $._expr, ']'
    ),

    // [Nat -> Nat]
    set_of_functions: $ => seq(
      '[', $._expr, $.maps_to, $._expr, ']'
    ),

    // [foo |-> 0, bar |-> 1]
    record_literal: $ => seq(
      '[', commaList1(seq($.identifier, $.all_map_to, $._expr)), ']'
    ),

    // [foo : {0, 1}, bar : {0, 1}]
    set_of_records: $ => seq(
      '[', commaList1(seq($.identifier, ':', $._expr)), ']'
    ),

    // r.val
    record_value: $ => prec.left('17-17', seq($._expr, '.', $.identifier)),

    // [f EXCEPT !.foo[bar].baz = 4, !.bar = 3]
    except: $ => seq(
      '[', $._expr, 'EXCEPT',
      commaList1(seq('!', $._except_val, '=', $._expr)),
      ']'
    ),

    // .foo[bar].baz
    _except_val: $ => repeat1(
      choice(
        seq('.', $.identifier),
        seq('[', commaList1($._expr), ']')
      )
    ),

    // [f EXCEPT ![2] = @ + 1]
    prev_func_val: $ => '@',

    // <<1,2,3,4,5>>, <<>>
    tuple_literal: $ => seq(
      $.langle_bracket,
      commaList($._expr),
      $.rangle_bracket
    ),

    // [x ' > x]_<<x>>
    step_expr_or_stutter: $ => seq(
      '[', $._expr, ']_', $._subscript_expr
    ),

    // <<x' > x>>_<<x>>
    step_expr_no_stutter: $ => seq(
      $.langle_bracket,
      $._expr,
      $.rangle_bracket_sub,
      $._subscript_expr
    ),

    // WF_vars(ActionName)
    fairness: $ => seq(
      choice('WF_', 'SF_'), $._subscript_expr, '(', $._expr, ')'
    ),

    // IF a > b THEN a ELSE b
    if_then_else: $ => prec('0-0', seq(
      'IF', field('if', $._expr),
      'THEN', field('then', $._expr),
      'ELSE', field('else', $._expr)
    )),

    // CASE x = 1 -> "1" [] x = 2 -> "2" [] OTHER -> "3"
    // This exhibits dangling else parsing ambiguity; consider
    // CASE e -> CASE f -> g [] h -> i
    // This can be parsed as:
    // (1) CASE e -> (CASE f -> g) [] h -> i 
    // (2) CASE e -> (CASE f -> g [] h -> i)
    // Parse (2) is used, making this right-associative
    case: $ => prec.right(seq(
      'CASE', $.case_arm,
      repeat(seq($.case_box, $.case_arm)),
      optional(seq($.case_box, $.other_arm))
    )),

    // p -> val
    case_arm: $ => prec('0-0', seq($._expr, $.case_arrow, $._expr)),

    // OTHER -> val
    other_arm: $ => prec('0-0', seq('OTHER', $.case_arrow, $._expr)),

    // LET x == 5 IN 2*x
    let_in: $ => prec('0-0', seq(
      'LET',
      field('definitions', repeat1(choice(
        $.operator_definition,
        $.function_definition,
        $.module_definition,
        $.recursive_declaration
      ))),
      'IN',
      field('expression', $._expr)
    )),

    // This makes use of the external scanner.
    // /\ x
    // /\ y
    conj_list: $ => seq(
      $._indent,
      repeat1($.conj_item),
      $._dedent
    ),

    // /\ x
    conj_item: $ => seq($.bullet_conj, $._expr),

    // This makes use of the external scanner.
    // \/ x
    // \/ y
    disj_list: $ => seq(
      $._indent,
      repeat1($.disj_item),
      $._dedent
    ),

    // \/ x
    disj_item: $ => seq($.bullet_disj, $._expr),

    /************************************************************************/
    /* PREFIX, INFIX, AND POSTFIX OPERATOR DEFINITIONS                      */
    /************************************************************************/

    // Prefix operator symbols and their unicode equivalents.
    lnot:             $ => choice('\\lnot', '\\neg', '~', '¬'),
    union:            $ => 'UNION',
    powerset:         $ => 'SUBSET',
    domain:           $ => 'DOMAIN',
    negative:         $ => '-',
    negative_dot:     $ => '-.',
    enabled:          $ => 'ENABLED',
    unchanged:        $ => 'UNCHANGED',
    always:           $ => choice('[]', '□'),
    eventually:       $ => choice('<>', '⋄'),

    // Use rule when using ops as higher-order constructs.
    // Negative is disambiguated from minus with a '.'
    prefix_op_symbol: $ => choice(
      $.lnot,     $.union,      $.powerset,   $.domain,
      $.enabled,  $.unchanged,  $.always,     $.eventually,
      alias($.negative_dot, $.negative)
    ),

    // All bound prefix operators.
    // Prefix operators are given highest value in precedence range.
    // Precedence defined on p271 of Specifying Systems.
    bound_prefix_op: $ => choice(
      prefixOpPrec('4-4',   $._expr,  $.lnot),
      prefixOpPrec('8-8',   $._expr, choice($.union, $.powerset)),
      prefixOpPrec('9-9',   $._expr, $.domain),
      prefixOpPrec('12-12', $._expr, $.negative),
      prefixOpPrec('15-15', $._expr, choice(
        $.enabled, $.unchanged, $.always, $.eventually))
    ),

    // Infix operator symbols and their unicode equivalents.
    implies:          $ => choice('=>', '⟹', '⇒'),
    plus_arrow:       $ => choice('-+->', '⇸', '⥅'),
    equiv:            $ => choice('\\equiv', '≡'),
    iff:              $ => choice('<=>', '⟺', '⇔'),
    leads_to:         $ => choice('~>', '⇝', '↝'),
    land:             $ => choice('/\\', '\\land', '∧'),
    lor:              $ => choice('\\/', '\\lor', '∨'),
    assign:           $ => choice(':=', '≔'),
    bnf_rule:         $ => choice('::=', '⩴'),
    eq:               $ => '=',
    neq:              $ => choice('/=', '#', '≠'),
    lt:               $ => '<',
    gt:               $ => '>',
    leq:              $ => choice('<=', '=<', '\\leq', '≤'),
    geq:              $ => choice('>=', '\\geq', '≥'),
    approx:           $ => choice('\\approx', '≈'),
    rs_ttile:         $ => choice('|-', '⊢'),
    rd_ttile:         $ => choice('|=', '⊨'),
    ls_ttile:         $ => choice('-|', '⊣'),
    ld_ttile:         $ => choice('=|', '⫤'),
    asymp:            $ => choice('\\asymp', '≍'),
    cong:             $ => choice('\\cong', '≅'),
    doteq:            $ => choice('\\doteq', '≐'),
    gg:               $ => choice('\\gg', '≫'),
    ll:               $ => choice('\\ll', '≪'),
    in:               $ => choice('\\in', '∈'),
    notin:            $ => choice('\\notin', '∉'),
    prec:             $ => choice('\\prec', '≺'),
    succ:             $ => choice('\\succ', '≻'),
    preceq:           $ => choice('\\preceq', '⪯'),
    succeq:           $ => choice('\\succeq', '⪰'),
    propto:           $ => choice('\\propto', '∝'),
    sim:              $ => choice('\\sim', '∼'),
    simeq:            $ => choice('\\simeq', '≃'),
    sqsubset:         $ => choice('\\sqsubset', '⊏'),
    sqsupset:         $ => choice('\\sqsupset', '⊐'),
    sqsubseteq:       $ => choice('\\sqsubseteq', '⊑'),
    sqsupseteq:       $ => choice('\\sqsupseteq', '⊒'),
    subset:           $ => choice('\\subset', '⊂'),
    supset:           $ => choice('\\supset', '⊃'),
    subseteq:         $ => choice('\\subseteq', '⊆'),
    supseteq:         $ => choice('\\supseteq', '⊇'),
    compose:          $ => '@@',
    map_to:           $ => ':>',
    map_from:         $ => '<:',
    setminus:         $ => '\\',
    cap:              $ => choice('\\cap', '\\intersect', '∩'),
    cup:              $ => choice('\\cup', '\\union', '∪'),
    dots_2:           $ => choice('..', '‥'),
    dots_3:           $ => choice('...', '…'),
    plus:             $ => '+',
    plusplus:         $ => '++',
    oplus:            $ => choice('\\oplus', '(+)', '⊕'),
    ominus:           $ => choice('\\ominus', '(-)', '⊖'),
    mod:              $ => '%',
    modmod:           $ => '%%',
    vert:             $ => '|',
    vertvert:         $ => choice('||', '‖'),
    minus:            $ => '-',
    minusminus:       $ => '--',
    amp:              $ => '&',
    ampamp:           $ => '&&',
    odot:             $ => choice('\\odot', '(.)', '⊙'),
    oslash:           $ => choice('\\oslash', '(/)', '⊘'),
    otimes:           $ => choice('\\otimes', '(\\X)', '⊗'),
    mul:              $ => '*',
    mulmul:           $ => '**',
    slash:            $ => '/',
    slashslash:       $ => '//',
    bigcirc:          $ => choice('\\bigcirc', '◯'),
    bullet:           $ => choice('\\bullet', '●'),
    div:              $ => choice('\\div', '÷'),
    circ:             $ => choice('\\o', '\\circ', '∘'),
    star:             $ => choice('\\star', '⋆'),
    excl:             $ => choice('!!', '‼'),
    qq:               $ => choice('??', '⁇'),
    hashhash:         $ => '##',
    dol:              $ => '$',
    doldol:           $ => '$$',
    sqcap:            $ => choice('\\sqcap', '⊓'),
    sqcup:            $ => choice('\\sqcup', '⊔'),
    uplus:            $ => choice('\\uplus', '⊎'),
    times:            $ => choice('\\X', '\\times', '×'),
    wr:               $ => choice('\\wr', '≀'),
    cdot:             $ => choice('\\cdot', '⋅'),
    pow:              $ => '^',
    powpow:           $ => '^^',

    // All infix operator symbols.
    infix_op_symbol: $ => choice(
      $.implies,      $.plus_arrow,     $.equiv,        $.iff,
      $.leads_to,     $.land,           $.lor,          $.assign,
      $.bnf_rule,     $.eq,             $.neq,          $.lt,
      $.gt,           $.leq,            $.geq,          $.approx,
      $.rs_ttile,     $.rd_ttile,       $.ls_ttile,     $.ld_ttile,
      $.asymp,        $.cong,           $.doteq,        $.gg,
      $.ll,           $.in,             $.notin,        $.prec,
      $.succ,         $.preceq,         $.succeq,       $.sim,
      $.simeq,        $.sqsubset,       $.sqsupset,     $.sqsubseteq,
      $.sqsupseteq,   $.compose,        $.map_to,       $.map_from,
      $.setminus,     $.cap,            $.cup,          $.dots_2,
      $.dots_3,       $.plus,           $.plusplus,     $.oplus,
      $.ominus,       $.mod,            $.modmod,       $.vert,
      $.vertvert,     $.minus,          $.minusminus,   $.amp,
      $.ampamp,       $.odot,           $.oslash,       $.otimes,
      $.mul,          $.mulmul,         $.slash,        $.slashslash,
      $.bigcirc,      $.bullet,         $.div,          $.circ,
      $.star,         $.excl,           $.hashhash,     $.dol,
      $.doldol,       $.qq,             $.sqcap,        $.sqcup,
      $.uplus,        $.wr,             $.cdot,         $.pow,
      $.powpow,
    ),

    // Infix operators are given highest value in precedence range for parsing.
    // Infix operators are all marked as left-associative for parsing purposes.
    // Operator precedence range & associativity conflicts must be enforced
    // on semantic level. Precedence defined on p271 of Specifying Systems.
    bound_infix_op: $ => choice(
      infixOpPrec('1-1',  $._expr,
        $.implies),
      infixOpPrec('2-2',    $._expr, choice(
        $.plus_arrow, $.equiv, $.iff, $.leads_to)),
      infixOpPrec('3-3',    $._expr, choice(
        $.land, $.lor)),
      infixOpPrec('5-5',    $._expr, choice(
        $.assign,     $.bnf_rule, $.eq,       $.neq,      $.lt,
        $.gt,         $.leq,      $.geq,      $.approx,   $.rs_ttile,
        $.rd_ttile,   $.ls_ttile, $.ld_ttile, $.asymp,    $.cong,
        $.doteq,      $.gg,       $.ll,       $.in,       $.notin,
        $.prec,       $.succ,     $.preceq,   $.succeq,   $.propto,
        $.sim,        $.simeq,    $.sqsubset, $.sqsupset, $.sqsubseteq,
        $.sqsupseteq, $.subset,   $.supset,   $.subseteq, $.supseteq)),
      infixOpPrec('6-6',    $._expr,
        $.compose),
      infixOpPrec('7-7',    $._expr, choice(
        $.map_to, $.map_from)),
      infixOpPrec('8-8',    $._expr, choice(
        $.setminus, $.cap, $.cup)),
      infixOpPrec('9-9',    $._expr, choice(
        $.dots_2, $.dots_3)),
      infixOpPrec('10-10',  $._expr, choice(
        $.plus, $.plusplus, $.oplus)),
      infixOpPrec('11-11',  $._expr, choice(
        $.ominus,   $.mod,    $.modmod,     $.vert,
        $.vertvert, $.minus,  $.minusminus)),
      infixOpPrec('13-13',  $._expr, choice(
        $.amp,      $.ampamp, $.odot,     $.oslash,     $.otimes,
        $.mul,      $.mulmul, $.slash,    $.slashslash, $.bigcirc,
        $.bullet,   $.div,    $.circ,     $.star,       $.excl,
        $.hashhash, $.dol,    $.doldol,   $.qq,         $.sqcap,
        $.sqcup,    $.uplus,  $.times)),
      infixOpPrec('14-14',  $._expr, choice(
        $.wr, $.cdot, $.pow, $.powpow)),
    ),

    // Postfix operator symbols and their unicode equivalents.
    sup_plus:         $ => choice('^+', '⁺'),
    asterisk:         $ => '^*',
    sup_hash:         $ => '^#',
    prime:            $ => '\'',

    // All postfix operator symbols.
    postfix_op_symbol: $ => choice(
      $.sup_plus, $.asterisk, $.sup_hash, $.prime
    ),

    // All bound postfix operators.
    // Precedence defined on p271 of Specifying Systems.
    bound_postfix_op: $ => choice(
      postfixOpPrec('15-15', $._expr, choice(
        $.sup_plus, $.asterisk, $.sup_hash, $.prime))
    ),

    /************************************************************************/
    /* PROOF CONSTRUCTS                                                     */
    /************************************************************************/

    // ASSUME C \in Nat
    assumption: $ => seq(
      choice('ASSUME', 'ASSUMPTION', 'AXIOM'),
      optional(seq($.identifier, $.def_eq)),
      $._expr
    ),

    // THEOREM Spec => []Safety
    theorem: $ => seq(
      choice('THEOREM', 'PROPOSITION', 'LEMMA', 'COROLLARY'),
      optional(seq($.identifier, $.def_eq)),
      choice($._expr, $.assume_prove),
      optional($._proof)
    ),

    // ASSUME NEW x \in Nat, NEW y \in Nat PROVE x + y \in Nat
    assume_prove: $ => seq(
      'ASSUME',
      field('assumption', commaList1(choice($._expr, $.new, $.inner_assume_prove))),
      'PROVE',
      field('conclusion', $._expr)
    ),

    // triangle ∷ ASSUME x > y, y > z PROVE x > z
    inner_assume_prove: $ => seq(
      optional(seq($.identifier, $.label_as)),
      $.assume_prove
    ),

    // NEW CONSTANT x \in Nat
    new: $ => seq(
      oneOrBoth('NEW', $.level),
      choice(
        seq($.identifier, $.set_in, $._expr),
        $._id_or_op_declaration
      )
    ),

    // The scope level of an introduction
    level: $ => choice(
      'CONSTANT', 'VARIABLE', 'STATE', 'ACTION', 'TEMPORAL'
    ),

    _proof: $ => choice(
      $.terminal_proof,
      $.non_terminal_proof
    ),

    // PROOF BY z \in Nat
    terminal_proof: $ => seq(
      optional(alias($.proof_keyword, 'PROOF')),
      choice(
        seq(alias($.by_keyword, 'BY'), optional('ONLY'), $.use_body),
        alias($.obvious_keyword, 'OBVIOUS'),
        alias($.omitted_keyword, 'OMITTED')
      )
    ),

    non_terminal_proof: $ => seq(
      optional(alias($.proof_keyword, 'PROOF')),
      $._begin_proof,
      repeat($.proof_step),
      $.qed_step
    ),

    // A single step in a proof. Can be many things!
    proof_step: $ => seq(
      $._begin_proof_step,
      $.proof_step_id,
      choice(
        $.definition_proof_step,
        $.have_proof_step,
        $.witness_proof_step,
        $.take_proof_step,
        $.suffices_proof_step,
        $.case_proof_step,
        $.pick_proof_step,
        $.use_or_hide,
        $.instance
      )
    ),

    // Proof step defining a new unit symbol.
    definition_proof_step: $ => seq(
      optional('DEFINE'),
      repeat1(
        choice(
          $.operator_definition,
          $.function_definition,
          $.module_definition
        )
      )
    ),

    have_proof_step: $ => seq('HAVE', $._expr),
    witness_proof_step: $ => seq('WITNESS', commaList1($._expr)),
    take_proof_step: $ => seq('TAKE', $._bound_or_identifier_list),
    suffices_proof_step: $ => seq(
      optional('SUFFICES'), choice($._expr, $.assume_prove), optional($._proof)
    ),
    case_proof_step: $ => seq('CASE', $._expr, optional($._proof)),
    pick_proof_step: $ => seq(
      'PICK', $._bound_or_identifier_list, ':', $._expr,
      optional($._proof)
    ),

    // One of:
    //   a, b, c, d
    //   a \in P, b, c \in Q, d, e, f \in R
    _bound_or_identifier_list: $ => choice(
      commaList1($.quantifier_bound),
      commaList1($.identifier)
    ),

    // <*> QED
    qed_step: $ => seq(
      $._begin_proof_step,
      $.proof_step_id,
      alias($.qed_keyword, 'QED'),
      optional($._proof)
    ),

    use_or_hide: $ => seq(
      choice(
        seq('USE', optional('ONLY')),
        'HIDE'
      ),
      $.use_body
    ),

    use_body: $ => oneOrBoth($.use_body_expr, $.use_body_def),

    // P, MODULE Naturals, Q, MODULE Integers
    use_body_expr: $ => commaList1(choice($._expr, $.module_ref)),
    
    // DEFS >, R, MODULE Reals, =
    use_body_def: $ => seq(
      choice('DEF', 'DEFS'),
      commaList1(choice($._op_or_expr, $.module_ref))
    ),

    module_ref: $ => seq('MODULE', alias($.identifier, $.identifier_ref)),

    // <+>foo22..
    // Used when writing another proof step
    // proof_step_id: $ => /<(\d+|\+|\*)>[\w|\d]*\.*/,
    proof_step_id: $ => seq(
      '<',
      alias(token.immediate(/\d+|\+|\*/), $.level),
      token.immediate('>'),
      alias(token.immediate(/[\w|\d]*/), $.name),
      token.immediate(/\.*/)
    ),

    // Used when referring to a prior proof step
    // proof_step_ref: $ => /<(\d+|\*)>[\w|\d]+/,
    proof_step_ref: $ => seq(
      '<',
      alias(token.immediate(/\d+|\*/), $.level),
      token.immediate('>'),
      alias(token.immediate(/[\w|\d]+/), $.name),
    ),

    /**************************************************************************/
    /* PlusCal: written inside block comments and transpiled into TLA+.       */
    /* According to the BNF from p. 60-62 of the p-manual                     */
    /* (https://lamport.azurewebsites.net/tla/p-manual.pdf)                   */
    /**************************************************************************/

    // PlusCal algorithm definition:
    // --algorithm foo
    //   *variable declarations*
    //   *define section*
    //   *macro declarations*
    //   *procedure declarations*
    //   *algorithm body* or *PlusCal processes*
    // end algorithm;
    pcal_algorithm: $ => seq(
      choice('--algorithm', seq('--fair', 'algorithm')),
      field('name', $.identifier),
      optional($.pcal_var_decls),
      optional($.pcal_definitions),
      repeat($.pcal_macro),
      repeat($.pcal_procedure),
      choice($.pcal_algorithm_body, repeat1($.pcal_process)),
      'end', 'algorithm', optional(';'),
    ),

    // Consequent statements with an optional semicolon at the end:
    // await initialized[self];
    // A:+ call my_procedure();
    // x := y || y := x
    _pcal_stmts: $ => seq(repeat(seq($._pcal_stmt, ';')), $._pcal_stmt, optional(';')),

    // Single statement, optionally prefixed with a label:
    // A:+ call my_procedure()
    _pcal_stmt: $ => seq(
      optional(seq(field('label', seq($.identifier, ':')), optional(choice('+', '-')))),
      $._pcal_unlabeled_stmt
    ),

    // Operators, which depend on PlusCal variables
    // define 
    //   zy == y*(x+y)
    // end define ;
    pcal_definitions: $ => seq(
      'define',
      repeat1($._definition),
      'end', 'define', optional(';')
    ),

    // macro go(routine) begin
    //   initialized[routine] := TRUE;
    // end macro
    pcal_macro: $ => seq(
      'macro', field('name', $.identifier),
      '(',
      optional(seq(
        field('parameter', $.identifier), 
        repeat(seq(',', field('parameter', $.identifier)))
      )),
      ')',
      $.pcal_algorithm_body,
      'end', 'macro', optional(';')
    ),

    // procedure foo(x=0) begin
    //   Send:
    //     await x \notin cs;
    //     return;
    // end procedure
    pcal_procedure: $ => seq(
      'procedure', field('name', $.identifier),
      '(',
      optional(seq($.pcal_p_var_decl, repeat(seq(',', $.pcal_p_var_decl)))),
      ')',
      optional($.pcal_p_var_decls),
      $.pcal_algorithm_body,
      'end', 'procedure', optional(';')
    ),

    // fair+ process bar in 1..10
    // variables i = 0;
    // begin
    // A:
    //   i := i +1;
    //   print(i);
    // end process
    pcal_process: $ => seq(
      optional(seq('fair', optional('+'))),
      'process', field('name', $.identifier),
      choice('=', $.set_in),
      $._expr,
      optional($.pcal_var_decls),
      $.pcal_algorithm_body,
      'end', 'process', optional(';')
    ),

    // variables x = 0; y = [a |-> "a", b |-> {}];
    pcal_var_decls: $ => seq(
      choice('variable', 'variables'),
      repeat1($.pcal_var_decl)
    ),

    // x \in 1..10 
    // x = "x"
    pcal_var_decl: $ => seq(
      $.identifier,
      optional(seq(choice('=', '\in'), $._expr)),
      choice(';', ',')
    ),

    // Procedure local variables:
    // variables x=1..10, y=1;
    pcal_p_var_decls: $ => seq(
      choice('variable', 'variables'),
      repeat1(seq($.pcal_p_var_decl, choice(';', ',')))
    ),

    // Procedure variable or parameter, maybe with a default value:
    // procedure foo(a, b=1)
    //               🠑   🠑
    // variable x=1;
    //           🠑 
    pcal_p_var_decl: $ => seq(
      $.identifier,
      optional(seq('=', $._expr))
    ),
    pcal_algorithm_body: $ => seq(
      'begin',
      $._pcal_stmts
    ),

    // Single statement:
    // with x \in xs do
    //   print(x);
    // end with
    _pcal_unlabeled_stmt: $ => choice(
      $.pcal_assign,
      $.pcal_if,
      $.pcal_while,
      $.pcal_either,
      $.pcal_with,
      $.pcal_await,
      $.pcal_print,
      $.pcal_assert,
      $.pcal_skip,
      $.pcal_return,
      $.pcal_goto,
      $.pcal_call,
      $.pcal_macro_call,
    ),

    // x[i] := x[j] || a := b
    pcal_assign: $ => seq(
      $.pcal_lhs, 
      $.assign,
      $._expr,
      repeat(seq($.vertvert, $.pcal_lhs, $.assign, $._expr))
    ),

    // Left part of assignment:
    // x[i]
    pcal_lhs: $ => seq(
      alias($.identifier, $.identifier_ref),
      repeat(choice(
        seq('[', $._expr, repeat(seq(',', $._expr)), ']'),
        seq('.', $.identifier)
      ))
    ),

    // if test1 then
    //   clause1
    // elseif test2 then
    //   clause2
    // else 
    //   clause3
    // end if
    pcal_if: $ => seq(
      'if', $._expr, 'then',
      $._pcal_stmts,
      repeat(seq('elseif', $._expr, 'then', $._pcal_stmts)),
      optional(seq('else', $._pcal_stmts)),
      alias('end', $.pcal_end_if), 'if'
    ),

    // while i <= 10 do
    //   i := i + 1;
    // end while;
    pcal_while: $ => seq(
      'while', $._expr,
      'do',
      $._pcal_stmts,
      alias('end', $.pcal_end_while), 'while'
    ),

    // Process branching operator:
    // either clause1
    //     or clause2
    //     or clause3
    // end either
    pcal_either: $ => seq(
      'either',
      $._pcal_stmts,
      repeat1(seq('or', $._pcal_stmts)),
      alias('end', $.pcal_end_either), 'either'
    ),

    // with id \in S do body end with 
    pcal_with: $ => seq(
      'with',
      repeat(seq(
        $.identifier,
        choice('=', $.set_in),
        $._expr,
        choice(',', ';')
      )),
      seq(
        $.identifier,
        choice('=', $.set_in),
        $._expr,
        optional(choice(',', ';'))
      ),
      'do',
      $._pcal_stmts,
      alias('end', $.pcal_end_with), 'with'
    ),

    // await channels[chan] /= {};
    pcal_await: $ => seq(
      choice('await', 'when'),
      $._expr
    ),

    // print(expr)
    pcal_print: $ => seq('print', $._expr),

    // assert(test)
    pcal_assert: $ => seq('assert', $._expr),

    // Statement, that does nothing:
    // skip
    pcal_skip: $ => seq('skip'),

    // Used in procedures. Assigns to the parameters and local 
    // procedure variables their previous values
    // procedure foo(a=1) begin
    // variable b=2;
    //   a := b;
    //   return;
    // end procedure
    pcal_return: $ => seq('return'),

    // Jump to a label:
    // process foo begin
    //   A: 
    //     print("A");
    //   B:
    //     goto A;
    // end process
    pcal_goto: $ => seq('goto', field('statement', $.identifier)),

    // Procedure call:
    // call my_proc(param1, param2)
    pcal_call: $ => seq('call', $.pcal_macro_call),

    // Macro call:
    // my_macro(param1, param2)
    pcal_macro_call: $ => seq(
      field('name', $.identifier), '(',
      optional(seq($._expr, repeat(seq(',', $._expr)))),
      ')'
    ),
  }
});
