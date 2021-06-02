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
  return seq(op, optional(seq('(', commaList1(expr), ')')))
}

// A rule matching either the first or second rule, or the first then the
// second rule, but not matching nothing.
function oneOrBoth(first, second) {
  return choice(first, second, seq(first, second))
}

// Defines a labelled prefix operator of given precedence
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

module.exports = grammar({
  name: 'tlaplus',

  extras: $ => [
    /\s|\r?\n/,
    $.single_line_comment,
    $.multi_line_comment
  ],

  conflicts: $ => [
    // Lookahead to disambiguate '-'  •  '('  …
    [$.minus, $.negative],
    // Lookahead to disambiguate '/\'  •  '('  …
    [$.bullet_conj, $.land],
    // Lookahead to disambiguate '\/'  •  '('  …
    [$.bullet_disj, $.lor],
    // Lookahead to disambiguate name  •  '('  …
    [$.identifier, $.label],
    // Lookahead to disambiguate '['  identifier  •  '\in'  …
    // Matches both step_expr_or_stutter and function_value
    [$.bound_general_op, $.quantifier_bound],
    // Lookahead to disambiguate '{'  identifier  •  '\in'  …
    // Matches set_filter, set_map, and finite_set_literal
    [$.bound_general_op, $.single_quantifier_bound],
    // Lookahead to disambiguate '['  langle_bracket  identifier  •  '>>'  …
    // Matches step_expr_or_stutter and function_value
    [$.bound_general_op, $.tuple_of_identifiers],
    // Lookahead to disambiguate 'SF_'  identifier  •  '('  …
    // Could be SF_f(x)(e) or could be SF_f(e)
    [$.bound_general_op, $.subexpr_component],
    // Lookahead to disambiguate identifier  •  '\in'  …
    // Could be x \in y == ... (op def'n) or x \in S (expression)
    [$.bound_general_op, $.operator_definition],
    // Lookahead to disambiguate identifier  '('  identifier  •  ','  …
    // Could be op(a, b) == ... (decl'n) or op(a, b) (expression)
    [$.bound_general_op, $.operator_declaration],
    // Lookahead to disambiguate identifier  •  '['  …
    // Could be f[x \in S] == ... (function def'n) or f[x] (application)
    [$.bound_general_op, $.function_definition],
    // Lookahead to disambiguate 'SF_'  subexpr_prefix  identifier  •  '('  …
    // Could be SF_f(x)!g(y)(e) or could be SF_f(x)(e)
    [$.bound_general_op],
    // Lookahead to disambiguate subexpr_component  '!'  •  '\in'  …
    // The '\in' could be followed by a ! or it could be the end
    [$.subexpr_prefix],
    // Lookahead to disambiguate begin_proof_step_token  _expr  •
    // begin_proof_step_token  …
    // Could be <1>a QED or could be <1>a (proof continues)
    [$.proof_step],
    // Lookahead to disambiguate begin_proof_step_token  'QED'  •
    // begin_proof_step_token  …
    // Proof can follow a QED statement; is this a grammar bug?
    [$.qed_step]
  ],

  rules: {
    source_file: $ => $.module,
    //source_file: $ => $._expr,

    // \* this is a comment ending with newline
    single_line_comment: $ => /\\\*.*/,

    // (* this is a multi-line comment *)
    // Taken from https://stackoverflow.com/a/36328890/2852699
    multi_line_comment: $ => /\(\*[^*]*\*+([^)*][^*]*\*+)*\)/,

    // Top-level module declaration
    module: $ => seq(
        $._single_line, 'MODULE', field('name', $.name), $._single_line,
        optional($.extends),
        repeat($.unit),
        $._double_line
    ),

    // Line of ---------- of length at least 4
    _single_line: $ => seq(
      '----',
      token.immediate(repeat(token.immediate('-')))
    ),

    // Line of =========== of length at least 4
    _double_line: $ => seq(
      '====',
      token.immediate(repeat(token.immediate('=')))
    ),

    // Various syntactic elements and their unicode equivalents
    def_eq:           $ => choice('==', '≜'),
    set_in:           $ => choice('\\in', '∈'),
    gets:             $ => choice('<-', '⟵'),
    forall:           $ => choice('\\A', '\\forall', '∀'),
    exists:           $ => choice('\\E', '\\exists', '∃'),
    temporal_forall:  $ => choice('\\AA'),
    temporal_exists:  $ => choice('\\EE'),
    all_map_to:       $ => choice('|->', '⟼'), 
    maps_to:          $ => choice('->', '⟶'),
    langle_bracket:   $ => choice('<<', '〈'),
    rangle_bracket:   $ => choice('>>', '〉'),
    case_box:         $ => choice('[]', '□'),
    case_arrow:       $ => choice('->', '⟶'),
    bullet_conj:      $ => choice('/\\', '∧'),
    bullet_disj:      $ => choice('\\/', '∨'),
    colon:            $ => choice(':', '∶'),
    address:          $ => '@',
    label_as:         $ => choice('::', '∷'),
    placeholder:      $ => '_',

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

    // Name (module, definition, etc.)
    // Can contain letters, numbers, and underscores
    // If only one character long, must be letter (not number or _)
    name: $ => /\w*[A-Za-z]\w*/,

    // General-purpose identifier, should exclude reserved keywords,
    // but tree-sitter currently does not support match exclusion logic.
    identifier: $ => $.name,

    // EXTENDS Naturals, FiniteSets, Sequences
    extends: $ => seq('EXTENDS', commaList1($.name)),

    // A module-level definition
    unit: $ => choice(
        $.variable_declaration,
        $.constant_declaration,
        $.recursive_operator_declaration,
        seq(optional("LOCAL"), $.operator_definition),
        seq(optional("LOCAL"), $.function_definition),
        seq(optional("LOCAL"), $.instance),
        seq(optional("LOCAL"), $.module_definition),
        $.assumption,
        $.theorem,
        $.module,
        $._single_line
    ),

    // VARIABLES v1, v2, v3
    variable_declaration: $ => seq(
        choice('VARIABLE', 'VARIABLES'),
        commaList1($.identifier)
    ),

    // CONSTANTS C1, C2, C3
    constant_declaration: $ => seq(
        choice('CONSTANT', 'CONSTANTS'),
        commaList1($.operator_declaration)
    ),

    // RECURSIVE op(_, _)
    recursive_operator_declaration: $ => seq(
      'RECURSIVE', commaList1($.operator_declaration)
    ),

    // Operator declaration (not definition)
    // Used, for example, when op accepts another op as parameter
    // op, op(_,_), _+_, etc.
    operator_declaration: $ => choice(
      arity0OrN($.identifier, $.placeholder),
      seq($.standalone_prefix_op_symbol, $.placeholder),
      seq($.placeholder, $.infix_op_symbol, $.placeholder),
      seq($.placeholder, $.postfix_op_symbol)
    ),

    // Operator definition
    // max(a, b) == IF a > b THEN a ELSE b
    // a \prec b == a.val < b.val
    // x ≜ 〈 1, 2, 3, 4, 5 〉
    operator_definition: $ => seq(
      choice(
        arity0OrN($.identifier, $.operator_declaration),
        seq($.standalone_prefix_op_symbol, $.identifier),
        seq($.identifier, $.infix_op_symbol, $.identifier),
        seq($.identifier, $.postfix_op_symbol)
      ),
      $.def_eq,
      $._expr
    ),

    // f[x \in Nat] == 2*x
    function_definition: $ => seq(
      $.identifier,
      '[', commaList1($.quantifier_bound), ']',
      $.def_eq,
      $._expr
    ),

    // x, y, z \in S
    // <<x, y, z>> \in S \X T \X P
    quantifier_bound: $ => seq(
      choice(
        commaList1($.identifier),
        $.tuple_of_identifiers
      ),
      $.set_in,
      $._expr
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
      $.name,
      optional(seq('WITH', commaList1($.substitution)))
    ),

    // x <- y, w <- z
    substitution: $ => seq(
      choice(
        $.identifier,
        $.standalone_prefix_op_symbol,
        $.infix_op_symbol,
        $.postfix_op_symbol
      ),
      $.gets,
      $.op_or_expr
    ),

    // Either an operator (op, +, *, LAMBDA, etc.) or an expression
    op_or_expr: $ => choice(
      $.standalone_prefix_op_symbol,
      $.infix_op_symbol,
      $.postfix_op_symbol,
      $.lambda,
      $._expr
    ),

    // foo!bar!baz!
    subexpr_prefix: $ => seq(
      choice($.subexpr_component, $.proof_step_id), '!',
      repeat(seq(choice($.subexpr_component, $.subexpr_tree_nav), '!'))
    ),

    // Subexpression component referencing a previously-defined symbol
    // Can either bind parameters to the op or leave them unbound
    subexpr_component: $ => choice(
      arity0OrN($.identifier, $.op_or_expr),
      arity1($.standalone_prefix_op_symbol, $._expr),
      arity2($.infix_op_symbol, $._expr),
      arity1($.postfix_op_symbol, $._expr),
      $.standalone_prefix_op_symbol,
      $.infix_op_symbol,
      $.postfix_op_symbol
    ),

    // Metalanguage to navigate the parse tree of an expression
    // F!:!〈!〉!2!(0, 3)!@
    subexpr_tree_nav: $ => choice(
      $.langle_bracket,   // first parse node child
      $.rangle_bracket,   // second parse node child
      $.nat_number,       // nth parse node child
      $.colon,            // for recursive operators
      $.address,          // use unbound quantifier as lambda
      $.operator_args     // bind quantifier
    ),

    // ...!(a, b, c)!...
    operator_args: $ => seq(
      '(', commaList1($.op_or_expr), ')'
    ),

    // LAMBDA a, b, c : a + b * c
    lambda: $ => seq(
      'LAMBDA', commaList1($.identifier), ':', $._expr
    ),

    // M == INSTANCE ModuleName
    module_definition: $ => seq(
      arity0OrN($.identifier, $.operator_declaration),
      $.def_eq,
      $.instance
    ),

    /************************************************************************/
    /* EXPRESSIONS                                                          */
    /************************************************************************/

    // Anything that evaluates to a value
    _expr: $ => choice(
      $.number,
      $.string,
      $.boolean,
      $.parentheses,
      $.label,
      $.subexpression,
      $.proof_step_id,
      $.bound_general_op,
      $.bound_nonfix_op,
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
      $.function_value,
      $.set_of_functions,
      $.record_value,
      $.set_of_records,
      $.except,
      $.prev_func_val,
      $.tuple_literal,
      $.step_expr_or_stutter,
      $.step_expr_no_stutter,
      $.fairness,
      $.if_then_else,
      $.case,
      $.let_in,
      $.conj,
      $.disj,
    ),

    // Expressions allowed in subscripts; must be enclosed in delimiters
    // Used in WF_expr, <><<f>>_expr, etc.
    _subscript_expr: $ => choice(
      $.bound_general_op,
      $.parentheses,
      $.finite_set_literal,
      $.set_filter,
      $.set_map,
      $.function_value,
      $.set_of_functions,
      $.record_value,
      $.set_of_records,
      $.except,
      $.tuple_literal,
      $.step_expr_or_stutter,
      $.step_expr_no_stutter,
    ),

    bound_general_op: $ => seq(
      optional($.subexpr_prefix),
      arity0OrN($.identifier, $.op_or_expr)
    ),

    bound_nonfix_op: $ => seq(
      optional($.subexpr_prefix),
      choice(
        arity1($.standalone_prefix_op_symbol, $._expr),
        arity2($.infix_op_symbol, $._expr),
        arity1($.postfix_op_symbol, $._expr)
      )
    ),

    // Number literal encodings
    number: $ => choice(
      $.nat_number,     $.real_number,
      $.binary_number,  $.octal_number,   $.hex_number
    ),

    nat_number: $ => /\d+/,
    real_number: $ => /\d+\.\d+/,
    binary_number: $ => /(\\b|\\B)[0-1]+/,
    octal_number: $ => /(\\o|\\O)[0-7]+/,
    hex_number: $ => /(\\h|\\H)[0-9a-fA-F]+/,

    // "foobar", "", etc.
    string: $ => choice(/\".*\"/, 'STRING'),

    // TRUE, FALSE, BOOLEAN
    boolean: $ => choice('TRUE', 'FALSE', 'BOOLEAN'),

    label: $ => seq(
      arity0OrN($.name, $.identifier),
      $.label_as,
      $._expr
    ),

    subexpression: $ => seq(
      $.subexpr_prefix,
      $.subexpr_tree_nav
    ),

    // ((a + b) + c)
    parentheses: $ => seq('(', $._expr, ')'),

    // \A x \in Nat : P(x)
    bounded_quantification: $ => seq(
      field('quantifier', choice($.forall, $.exists)),
      field('bound', commaList1($.quantifier_bound)),
      ':',
      field('expression', $._expr)
    ),

    // \EE x : P(x)
    unbounded_quantification: $ => seq(
      field('quantifier', choice(
        $.forall, $.exists, $.temporal_forall, $.temporal_exists
      )),
      field('identifier', commaList1($.identifier)),
      ':',
      field('expression', $._expr)
    ),

    // CHOOSE r \in Real : r >= 0
    choose: $ => seq(
      'CHOOSE',
      choice($.identifier, $.tuple_of_identifiers),
      optional(seq($.set_in, $._expr)),
      ':',
      $._expr
    ),

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
    function_evaluation: $ => prec(16, seq(
      $._expr, '[', commaList1($._expr), ']'
    )),

    // [n \in Nat |-> 2*n]
    function_value: $ => seq(
      '[', commaList1($.quantifier_bound), $.all_map_to, $._expr, ']'
    ),

    // [Nat -> Nat]
    set_of_functions: $ => seq(
      '[', $._expr, $.maps_to, $._expr, ']'
    ),

    // [foo |-> 0, bar |-> 1]
    record_value: $ => seq(
      '[', commaList1(seq($.name, $.all_map_to, $._expr)), ']'
    ),

    // [foo : {0, 1}, bar : {0, 1}]
    set_of_records: $ => seq(
      '[', commaList1(seq($.name, ':', $._expr)), ']'
    ),

    // [f EXCEPT !.foo[bar].baz = 4, !.bar = 3]
    except: $ => seq(
      '[', $._expr, 'EXCEPT',
      commaList1(seq('!', $._except_val, '=', $._expr)),
      ']'
    ),

    // .foo[bar].baz
    _except_val: $ => repeat1(
      choice(
        seq('.', $.name),
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
      $.rangle_bracket, token.immediate('_'),
      $._subscript_expr
    ),

    // WF_vars(ActionName)
    fairness: $ => seq(
      choice('WF_', 'SF_'), $._subscript_expr, '(', $._expr, ')'
    ),

    // IF a > b THEN a ELSE b
    if_then_else: $ => seq(
      'IF', field('if', $._expr),
      'THEN', field('then', $._expr),
      'ELSE', field('else', $._expr)
    ),

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
    case_arm: $ => seq($._expr, $.case_arrow, $._expr),

    // OTHER -> val
    other_arm: $ => seq('OTHER', $.case_arrow, $._expr),

    // LET x == 5 IN 2*x
    let_in: $ => seq(
      'LET',
      repeat1(
        choice(
          $.operator_definition,
          $.function_definition,
          $.module_definition,
          $.recursive_operator_declaration
        )
      ),
      'IN',
      $._expr
    ),

    // /\ x
    // /\ y
    // TODO: replace with context-sensitive parser
    conj: $ => prec.left(repeat1(seq($.bullet_conj, $._expr))),

    // \/ x
    // \/ y
    // TODO: replace with context-sensitive parser
    disj: $ => prec.left(repeat1(seq($.bullet_disj, $._expr))),

    /************************************************************************/
    /* PREFIX, INFIX, AND POSTFIX OPERATOR DEFINITIONS                      */
    /************************************************************************/

    // Prefix operator symbols and their unicode equivalents
    lnot:             $ => choice('\\lnot', '\\neg', '~', '¬'),
    union:            $ => 'UNION',
    subset:           $ => 'SUBSET',
    domain:           $ => 'DOMAIN',
    negative:         $ => '-',
    enabled:          $ => 'ENABLED',
    unchanged:        $ => 'UNCHANGED',
    always:           $ => choice('[]', '□'),
    eventually:       $ => choice('<>', '⋄'),

    _prefix_op_symbol_except_negative: $ => choice(
      $.lnot,     $.union,      $.subset,     $.domain,
      $.enabled,  $.unchanged,  $.always,     $.eventually
    ),

    // Use rule when using ops as higher-order constructs
    // Negative is disambiguated from minus with a '.'
    standalone_prefix_op_symbol: $ => choice(
      $._prefix_op_symbol_except_negative,
      seq($.negative, token.immediate('.'))
    ),

    // All bound prefix operators
    // Prefix operators are given highest value in precedence range
    bound_prefix_op: $ => choice(
      prefixOpPrec(4,   $._expr,  $.lnot),
      prefixOpPrec(8,   $._expr, choice($.union, $.subset)),
      prefixOpPrec(9,   $._expr, $.domain),
      prefixOpPrec(12,  $._expr, $.negative),
      prefixOpPrec(15,  $._expr, choice(
        $.enabled, $.unchanged, $.always, $.eventually))
    ),

    // Infix operator symbols and their unicode equivalents
    implies:          $ => choice('=>', '⟹'),
    plus_arrow:       $ => choice('-+->', '⇸'),
    equiv:            $ => choice('\\equiv', '≡'),
    iff:              $ => choice('<=>', '⟺'),
    leads_to:         $ => choice('~>', '⇝'),
    land:             $ => choice('/\\', '\\land', '∧'),
    lor:              $ => choice('\\/', '\\lor', '∨'),
    assign:           $ => choice(':=', '≔'),
    bnf_rule:         $ => choice('::=', '⩴'),
    eq:               $ => '=',
    neq:              $ => choice('/=', '#', '≠'),
    lt:               $ => '<',
    gt:               $ => '>',
    leq:              $ => choice('<=', '\\leq', '≤'),
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
    cap:              $ => choice('\\cap', '∩'),
    cup:              $ => choice('\\cup', '∪'),
    dots_2:           $ => choice('..', '‥'),
    dots_3:           $ => choice('...', '…'),
    plus:             $ => '+',
    plusplus:         $ => '++',
    oplus:            $ => choice('\\oplus', '⊕'),
    ominus:           $ => choice('\\ominus', '⊖'),
    mod:              $ => '%',
    modmod:           $ => '%%',
    vert:             $ => '|',
    vertvert:         $ => choice('||', '‖'),
    minus:            $ => '-',
    minusminus:       $ => '--',
    amp:              $ => '&',
    ampamp:           $ => '&&',
    odot:             $ => choice('\\odot', '⊙'),
    oslash:           $ => choice('\\oslash', '⊘'),
    otimes:           $ => choice('\\otimes', '⊗'),
    mul:              $ => '*',
    mulmul:           $ => '**',
    slash:            $ => '/',
    slashslash:       $ => '//',
    bigcirc:          $ => choice('\\bigcirc', '◯'),
    bullet:           $ => choice('\\bullet', '●'),
    div:              $ => choice('\\div', '÷'),
    circ:             $ => choice('\\circ', '∘'),
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
    rfield:           $ => '.',

    // All infix operator symbols
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
      $.powpow,       $.rfield
    ),

    // Infix operators are given highest value in precedence range for parsing
    // Infix operators are all marked as left-associative for parsing purposes
    // Operator precedence range & associativity conflicts must be enforced
    // on semantic level
    bound_infix_op: $ => choice(
      infixOpPrec(1, $._expr, choice(
        $.implies, $.plus_arrow)),
      infixOpPrec(2, $._expr, choice(
        $.equiv, $.iff, $.leads_to)),
      infixOpPrec(3, $._expr, choice(
        $.land, $.lor)),
      infixOpPrec(5, $._expr, choice(
        $.assign,     $.bnf_rule, $.eq,       $.neq,      $.lt,
        $.gt,         $.leq,      $.geq,      $.approx,   $.rs_ttile,
        $.rd_ttile,   $.ls_ttile, $.ld_ttile, $.asymp,    $.cong,
        $.doteq,      $.gg,       $.ll,       $.in,       $.notin,
        $.prec,       $.succ,     $.preceq,   $.succeq,   $.propto,
        $.sim,        $.simeq,    $.sqsubset, $.sqsupset, $.sqsubseteq,
        $.sqsupseteq, $.subset,   $.supset,   $.subseteq, $.supseteq)),
      infixOpPrec(6, $._expr,
        $.compose),
      infixOpPrec(7, $._expr, choice(
        $.map_to, $.map_from)),
      infixOpPrec(8, $._expr, choice(
        $.setminus, $.cap, $.cup)),
      infixOpPrec(9, $._expr, choice(
        $.dots_2, $.dots_3)),
      infixOpPrec(10, $._expr, choice(
        $.plus, $.plusplus, $.oplus)),
      infixOpPrec(11, $._expr, choice(
        $.ominus,   $.mod,    $.modmod,     $.vert,
        $.vertvert, $.minus,  $.minusminus)),
      infixOpPrec(13, $._expr, choice(
        $.amp,      $.ampamp, $.odot,     $.oslash,     $.otimes,
        $.mul,      $.mulmul, $.slash,    $.slashslash, $.bigcirc,
        $.bullet,   $.div,    $.circ,     $.star,       $.excl,
        $.hashhash, $.dol,    $.doldol,   $.qq,         $.sqcap,
        $.sqcup,    $.uplus,  $.times)),
      infixOpPrec(14, $._expr, choice(
        $.wr, $.cdot, $.pow, $.powpow)),
      infixOpPrec(14, $._expr,
        $.rfield)
    ),

    // Postfix operator symbols and their unicode equivalents
    sup_plus:         $ => choice('^+', '⁺'),
    asterisk:         $ => '^*',
    sup_hash:         $ => '^#',
    prime:            $ => '\'',

    // All postfix operator symbols
    postfix_op_symbol: $ => choice(
      $.sup_plus, $.asterisk, $.sup_hash, $.prime
    ),

    // All bound postfix operators
    bound_postfix_op: $ => choice(
      postfixOpPrec(15, $._expr, $.postfix_op_symbol)
    ),

    /************************************************************************/
    /* PROOF CONSTRUCTS                                                     */
    /************************************************************************/

    // ASSUME C \in Nat
    assumption: $ => seq(
      choice('ASSUME', 'ASSUMPTION', 'AXIOM'),
      optional(seq($.name, $.def_eq)),
      $._expr
    ),

    // THEOREM Spec => []Safety
    theorem: $ => seq(
      choice('THEOREM', 'PROPOSITION', 'LEMMA', 'COROLLARY'),
      optional(seq($.name, $.def_eq)),
      choice($._expr, $.assume_prove),
      optional($.proof)
    ),

    // ASSUME NEW x \in Nat, NEW y \in Nat PROVE x + y \in Nat
    assume_prove: $ => seq(
      'ASSUME',
      commaList1(choice($._expr, $.new, $.inner_assume_prove)),
      'PROVE',
      $._expr
    ),

    // triangle ∷ ASSUME x > y, y > z PROVE x > z
    inner_assume_prove: $ => seq(
      optional(seq($.name, $.label_as)),
      $.assume_prove
    ),

    // NEW CONSTANT x \in Nat
    new: $ => seq(
      oneOrBoth('NEW', $.level),
      choice(
        seq($.identifier, $.set_in, $._expr),
        $.operator_declaration
      )
    ),

    // The scope level of an introduction
    level: $ => choice(
      'CONSTANT', 'VARIABLE', 'STATE', 'ACTION', 'TEMPORAL'
    ),

    proof: $ => choice(
      $.terminal_proof,
      $.non_terminal_proof
    ),

    // PROOF BY z \in Nat
    terminal_proof: $ => choice(
      seq(optional('PROOF'), 'BY', optional('ONLY'), $.use_body),
      'OBVIOUS',
      'OMITTED'
    ),

    non_terminal_proof: $ => seq(
      optional('PROOF'),
      repeat($.proof_step),
      $.qed_step
    ),

    // A single step in a proof. Can be many things!
    proof_step: $ => seq(
      $.begin_proof_step_token,
      choice(
        choice(
          $.use_or_hide,
          seq(
            optional('DEFINE'),
            repeat1(
              choice(
                $.operator_definition,
                $.function_definition,
                $.module_definition
              )
            )
          ),
          $.instance,
          seq('HAVE', $._expr),
          seq('WITNESS', commaList1($._expr)),
          seq('TAKE', $.bound_or_identifier_list)
        ),
        seq(
          choice(
            seq(optional('SUFFICES'), choice($._expr, $.assume_prove)),
            seq('CASE', $._expr),
            seq('PICK', $.bound_or_identifier_list, ':', $._expr)
          ),
          optional($.proof)
        )
      )
    ),

    bound_or_identifier_list: $ => choice(
      commaList1($.quantifier_bound),
      commaList1($.identifier)
    ),

    // <*> QED
    qed_step: $ => seq(
      $.begin_proof_step_token,
      'QED',
      optional($.proof)
    ),

    use_or_hide: $ => seq(
      choice(
        seq('USE', optional('ONLY')),
        'HIDE'
      ),
      $.use_body
    ),

    use_body: $ => oneOrBoth($.use_body_expr, $.use_body_def),

    use_body_expr: $ => commaList1(
      choice(
        $._expr,
        seq('MODULE', $.name)
      )
    ),

    // DEFS foo, MODULE bar, baz
    use_body_def: $ => seq(
      choice('DEF', 'DEFS'),
      commaList1(choice(
        $.op_or_expr,
        seq('MODULE', $.name)
      ))
    ),

    // <+>foo22..
    // Used when writing another proof step
//    begin_proof_step_token: $ => seq(
//      '<',
//      field('level', token.immediate(/\d+|\+|\*/)),
//      token.immediate('>'),
//      field('name', token.immediate(/[\w|\d]*/)),
//      token.immediate(/\.*/)
//    ),

    begin_proof_step_token: $ => /<[\d+|\*|\+]>[\w|\d]+\.*/,

//    // Used when referring to a prior proof step
//    proof_step_id: $ => seq(
//      '<',
//      field('level', token.immediate(/\d+|\*/)),
//      token.immediate('>'),
//      field('name', token.immediate(/[\w|\d]+/))
//    ),

    proof_step_id: $ => /<[\d+|\*]>[\w|\d]+/
  }
});
