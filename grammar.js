// A sequence of one or more comma-separated strings matching the rule
function commaList1(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

// A sequence of zero or more comma-separated strings matching the rule
function commaList(rule) {
  return optional(commaList1(rule))
}

// Defines a labelled prefix operator of given precedence
function prefixOpPrec(level, prefix, expr, symbol) {
  return prec(level, seq(
    field('prefix', repeat(prefix)),
    field('symbol', symbol),
    field('rhs', expr)
  ))
}

// Defines a labelled left-associative infix operator of given precedence
function infixOpPrec(level, prefix, expr, symbol) {
  return prec.left(level, seq(
    field('lhs', expr),
    field('prefix', repeat(prefix)),
    field('symbol', symbol),
    field('rhs', expr)
  ))
}

// Defines a labelled postfix operator of given precedence
function postfixOpPrec(level, prefix, expr, symbol) {
  return prec(level, seq(
    field('lhs', expr),
    field('prefix', repeat(prefix)),
    field('symbol', symbol)
  ))
}

module.exports = grammar({
  name: 'tlaplus',

  conflicts: $ => [
    [$.general_identifier, $.tuple_of_identifiers],
    [$.general_identifier, $.instance_prefix],
    [$.general_identifier, $.quantifier_bound],
    [$.general_identifier, $.set_filter],
  ],

  rules: {
    //source_file: $ => repeat1($.module),
    source_file: $ => $._expr,

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

    // Identifier; should exclude reserved words
    identifier: $ => $.name,

    // <<x, y, z>>
    tuple_of_identifiers: $ => seq(
      $.langle_bracket,
      commaList1($.identifier),
      $.rangle_bracket
    ),

    // Number literal encodings
    number: $ => choice(
      /\d+/,                  // Natural numbers
      /\d+\.\d+/,             // Real numbers
      /(\\b|\\B)[0-1]+/,      // Binary numbers
      /(\\o|\\O)[0-7]+/,      // Octal numbers
      /(\\h|\\H)[0-9a-fA-F]+/ // Hexadecimal numbers
    ),

    // "foobar", "", etc.
    string: $ => /\".*\"/,

    // TRUE, FALSE, BOOLEAN
    boolean: $ => choice('TRUE', 'FALSE', 'BOOLEAN'),

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

    // All prefix operator symbols
    // Note negative is disambiguated from minus with a '.'
    prefix_op_symbol: $ => choice(
      $.lnot,     $.union,      $.subset,     $.domain,
      $.enabled,  $.unchanged,  $.always,     $.eventually,
      seq($.negative, token.immediate('.'))
    ),

    // Foo!\neg
    general_prefix_op: $ => seq(
      repeat($.instance_prefix), $.prefix_op_symbol
    ),

    // All bound prefix operators
    // Prefix operators are given highest value in precedence range
    bound_prefix_op: $ => choice(
      prefixOpPrec(4,   $.instance_prefix, $._expr,
        $.lnot),
      prefixOpPrec(8,   $.instance_prefix, $._expr, choice(
        $.union, $.subset)),
      prefixOpPrec(9,   $.instance_prefix, $._expr,
        $.domain),
      prefixOpPrec(12,  $.instance_prefix, $._expr,
        $.negative),
      prefixOpPrec(15,  $.instance_prefix, $._expr, choice(
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

    // Foo!+
    general_infix_op: $ => seq(
      repeat($.instance_prefix), $.infix_op_symbol
    ),

    // Infix operators are given highest value in precedence range for parsing
    // Infix operators are all marked as left-associative for parsing purposes
    // Operator precedence range & associativity conflicts must be enforced
    // on semantic level
    bound_infix_op: $ => choice(
      infixOpPrec(1, $.instance_prefix, $._expr, choice(
        $.implies, $.plus_arrow)),
      infixOpPrec(2, $.instance_prefix, $._expr, choice(
        $.equiv, $.iff, $.leads_to)),
      infixOpPrec(3, $.instance_prefix, $._expr, choice(
        $.land, $.lor)),
      infixOpPrec(5, $.instance_prefix, $._expr, choice(
        $.assign,     $.bnf_rule, $.eq,       $.neq,      $.lt,
        $.gt,         $.leq,      $.geq,      $.approx,   $.rs_ttile,
        $.rd_ttile,   $.ls_ttile, $.ld_ttile, $.asymp,    $.cong,
        $.doteq,      $.gg,       $.ll,       $.in,       $.notin,
        $.prec,       $.succ,     $.preceq,   $.succeq,   $.propto,
        $.sim,        $.simeq,    $.sqsubset, $.sqsupset, $.sqsubseteq,
        $.sqsupseteq, $.subset,   $.supset,   $.subseteq, $.supseteq)),
      infixOpPrec(6, $.instance_prefix, $._expr,
        $.compose),
      infixOpPrec(7, $.instance_prefix, $._expr, choice(
        $.map_to, $.map_from)),
      infixOpPrec(8, $.instance_prefix, $._expr, choice(
        $.setminus, $.cap, $.cup)),
      infixOpPrec(9, $.instance_prefix, $._expr, choice(
        $.dots_2, $.dots_3)),
      infixOpPrec(10, $.instance_prefix, $._expr, choice(
        $.plus, $.plusplus, $.oplus)),
      infixOpPrec(11, $.instance_prefix, $._expr, choice(
        $.ominus,   $.mod,    $.modmod,     $.vert,
        $.vertvert, $.minus,  $.minusminus)),
      infixOpPrec(13, $.instance_prefix, $._expr, choice(
        $.amp,      $.ampamp, $.odot,     $.oslash,     $.otimes,
        $.mul,      $.mulmul, $.slash,    $.slashslash, $.bigcirc,
        $.bullet,   $.div,    $.circ,     $.star,       $.excl,
        $.hashhash, $.dol,    $.doldol,   $.qq,         $.sqcap,
        $.sqcup,    $.uplus,  $.times)),
      infixOpPrec(14, $.instance_prefix, $._expr, choice(
        $.wr, $.cdot, $.pow, $.powpow)),
      infixOpPrec(14, $.instance_prefix, $._expr,
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

    // Foo!^#
    general_postfix_op: $ => seq(
      repeat($.instance_prefix), $.postfix_op_symbol
    ),

    // All bound postfix operators
    bound_postfix_op: $ => choice(
      postfixOpPrec(15, $.instance_prefix, $._expr, $.postfix_op_symbol)
    ),

    // Line of ---------- of length at least 4
    _single_line: $ => seq(
      '-',
      token.immediate('-'),
      token.immediate('-'),
      token.immediate('-'),
      token.immediate(token.immediate(repeat('-')))
    ),

    // Line of =========== of length at least 4
    _double_line: $ => seq(
      '=',
      token.immediate('='),
      token.immediate('='),
      token.immediate('='),
      token.immediate(token.immediate(repeat('=')))
    ),

    // Top-level module declaration
    module: $ => seq(
        $._single_line,
        'MODULE',
        $.name,
        $._single_line,
        optional($.extends),
        repeat($.unit),
        $._double_line
    ),

    // EXTENDS Naturals, FiniteSets, Sequences
    extends: $ => seq('EXTENDS', commaList1($.name)),

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
    // op, op(_, _), _+_, etc.
    operator_declaration: $ => choice(
      $.identifier,
      seq($.identifier, '(', commaList1('_'), ')'),
      seq($.prefix_op_symbol, '_'),
      seq('_', $.infix_op_symbol, '_'),
      seq('_', $.postfix_op_symbol)
    ),

    // Operator definition
    // max(a, b) == IF a > b THEN a ELSE b
    // a \prec b == a.val < b.val
    // x ≜ 〈 1, 2, 3, 4, 5 〉
    operator_definition: $ => seq(
      choice(
        $.non_fix_lhs,
        seq($.prefix_op_symbol, $.identifier),
        seq($.identifier, $.infix_op_symbol, $.identifier),
        seq($.identifier, $.postfix_op_symbol)
      ),
      $.def_eq,
      $._expr
    ),

    // Named operator left-hand-side, with or without parameters
    // op, op(a, b)
    non_fix_lhs: $ => seq(
      $.identifier,
      optional(seq(
        '(', commaList1($.operator_declaration), ')'
      )),
    ),

    // f[x \in Nat] == 2*x
    function_definition: $ => seq(
      $.identifier,
      '[', commaList1($.quantifier_bound), ']',
      $.def_eq,
      $._expr
    ),

    // x, y, z \in S
    quantifier_bound: $ => seq(
      choice(
        $.tuple_of_identifiers,
        commaList1($.identifier)
      ),
      $.set_in,
      $._expr
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
        $.prefix_op_symbol,
        $.infix_op_symbol,
        $.postfix_op_symbol
      ),
      $.gets,
      $.argument
    ),

    // An argument given to an operator
    argument: $ => choice(
      $._expr,
      $.general_prefix_op,
      $.general_infix_op,
      $.general_postfix_op
    ),

    // Foo(x, y)!Bar(w, z)!...
    instance_prefix: $ => seq(
      $.identifier,
      optional(seq('(', commaList1($._expr), ')')),
      '!'
    ),

    // Foo!bar
    general_identifier: $ => seq(
      repeat($.instance_prefix), $.identifier
    ),

    // M == INSTANCE ModuleName
    module_definition: $ => seq(
      $.non_fix_lhs,
      $.def_eq,
      $.instance
    ),

    // ASSUME C \in Nat
    assumption: $ => seq(
      choice('ASSUME', 'ASSUMPTION', 'AXIOM'),
      $._expr
    ),

    // THEOREM Spec => []Safety
    theorem: $ => seq('THEOREM', $._expr),

    // Anything that evaluates to a value
    _expr: $ => choice(
      $.general_identifier,
      $.bound_op,
      $.bound_prefix_op,
      $.bound_infix_op,
      $.bound_postfix_op,
      $.parentheses,
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
      $.stepexpression_or_stutter,
      $.stepexpression_no_stutter,
      //$.fairness,
      $.if_then_else,
      $.case,
      //$.let_in,
      //$.conj,
      //$.disj,
      $.string,
      $.number,
      $.boolean
    ),

    // max(2, 3)
    bound_op: $ => seq(
      field('name', $.general_identifier),
      '(', field('args', commaList1($.argument)), ')'),

    // ((a + b) + c)
    parentheses: $ => seq('(', $._expr, ')'),

    // \A x \in Nat : P(x)
    bounded_quantification: $ => seq(
      choice($.forall, $.exists),
      commaList1($.quantifier_bound), ':', $._expr
    ),

    // \EE x : P(x)
    unbounded_quantification: $ => seq(
      choice($.forall, $.exists, $.temporal_forall, $.temporal_exists),
      commaList1($.identifier), ':', $._expr
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
    set_filter: $ => seq(
      '{',
      field('generator', seq(
        choice($.identifier, $.tuple_of_identifiers),
        $.set_in,
        $._expr
      )),
      ':',
      field('filter', $._expr),
      '}'
    ),

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
      '[',
      $._expr,
      'EXCEPT',
      commaList1(
        seq(
          '!',
          repeat1(
            choice(
              seq('.', $.name),
              seq('[', commaList1($._expr), ']')
            )
          ),
          '=',
          $._expr
        )
      ),
      ']'
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
    stepexpression_or_stutter: $ => seq(
      '[', $._expr, ']_', $._expr
    ),

    // <<x' > x>>_<<x>>
    stepexpression_no_stutter: $ => seq(
      $.langle_bracket,
      $._expr,
      $.rangle_bracket, token.immediate('_'),
      $._expr
    ),

    // WF_vars(ActionName)
    fairness: $ => seq(
      choice('WF_', 'SF_'), $._expr, '(', $._expr, ')'
    ),

    // IF a > b THEN a ELSE b
    if_then_else: $ => seq(
      'IF', $._expr, 'THEN', $._expr, 'ELSE', $._expr
    ),

    // CASE x = 1 -> "1" [] x = 2 -> "2" [] OTHER -> "3"
    case: $ => prec.left(seq(
      'CASE', $._expr, $.case_arrow, $._expr,
      repeat(seq($.case_box, $._expr, $.case_arrow, $._expr)),
      optional(seq($.case_box, 'OTHER', $.case_arrow, $._expr))
    )),

    // LET x == 5 IN 2*x
    let_in: $ => seq(
      'LET',
      repeat1(
        choice(
          $.operator_definition,
          $.function_definition,
          $.module_definition
        )
      ),
      'IN',
      $._expr
    ),

    // /\ x
    // /\ y
    conj: $ => repeat1(seq($.bullet_conj, $._expr)),

    // \/ x
    // \/ y
    disj: $ => repeat1(seq($.bullet_disj, $._expr)),
  }
});
