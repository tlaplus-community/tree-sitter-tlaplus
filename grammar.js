function commaList1(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

function commaList(rule) {
  return optional(commaList1(rule))
}

module.exports = grammar({
  name: 'tlaplus',

  rules: {
    source_file: $ => repeat1($.module),

    reserved_word: $ => choice(
      'ASSUME',       'ELSE',       'LOCAL',      'UNION',
      'ASSUMPTION',   'ENABLED',    'MODULE',     'VARIABLE',
      'AXIOM',        'EXCEPT',     'OTHER',      'VARIABLES',
      'CASE',         'EXTENDS',    'SF_',        'WF_',
      'CHOOSE',       'IF',         'SUBSET',     'WITH',
      'CONSTANT',     'IN',         'THEN',
      'CONSTANTS',    'INSTANCE',   'THEOREM',
      'DOMAIN',       'LET',        'UNCHANGED'
    ),

    // Name (module, definition, etc.)
    // Can contain letters, numbers, and underscores
    // If only one character long, must be letter (not number or _)
    // Cannot begin with WF_ or SF_
    name: $ => /\b(?!WF_|SF_)\w*[A-Za-z]\w*/,

    // Identifier; should exclude reserved words
    identifier: $ => $.name,

    identifier_or_tuple: $ => choice(
      $.identifier,
      seq('<<', commaList1($.identifier), '>>')
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

    // Prefix operators
    prefix_op: $ => choice(
      '-',  '\\lnot', '[]', 'DOMAIN', 'ENABLED',  'UNION',
      '~',  '\\neg',  '<>', 'SUBSET', 'UNCHANGED'
    ),

    // Infix operators
    infix_op: $ => choice(
      '!!',   '#',    '##',   '$',    '$$',   '%',    '%%',
      '&',    '&&',   '(+)',  '(-)',  '(.)',  '(/)',  '(\\X)',
      '*',    '**',   '+',    '++',   '-',    '-+->', '--',
      '-|',   '..',   '...',  '/',    '//',   '/=',   '/\\',
      '::=',  ':=',   ':>',   '<',    '<:',   '<=>',  '=',
      '=<',   '=>',   '=|',   '>',    '>=',   '?',    '??',
      '@@',   '\\',   '\\/',  '^',    '^^',   '|',    '|-',
      '|=',   '||',   '~>',   '.',
      '\\approx',   '\\geq',        '\\oslash',     '\\sqsupseteq',
      '\\asymp',    '\\gg',         '\\otimes',     '\\star',
      '\\bigcirc',  '\\in',         '\\prec',       '\\subset',
      '\\bullet',   '\\intersect',  '\\preceq',     '\\subseteq',
      '\\cap',      '\\land',       '\\propto',     '\\succ',
      '\\cdot',     '\\leq',        '\\sim',        '\\succeq',
      '\\circ',     '\\ll',         '\\simeq',      '\\supset',
      '\\cong',     '\\lor',        '\\sqcap',      '\\supseteq',
      '\\cup',      '\\o',          '\\sqcup',      '\\union',
      '\\div',      '\\odot',       '\\sqsubset',   '\\uplus',
      '\\doteq',    '\\ominus',     '\\sqsubseteq', '\\wr',
      '\\equiv',    '\\oplus',      '\\sqsupset'
    ),

    // Postfix operators
    postfix_op: $ => choice('^+', '^*', '^#', '\''),

    // Line of ---------- of length at least 4
    single_line: $ => seq('-', '-', '-', '-', repeat('-')),

    // Line of =========== of length at least 4
    double_line: $ => seq('=', '=', '=', '=', repeat('=')),

    // Top-level module declaration
    module: $ => seq(
        $.single_line,
        'MODULE',
        $.name,
        $.single_line,
        optional($.extends),
        repeat($.unit),
        $.double_line
    ),

    // EXTENDS Naturals, FiniteSets, Sequences
    extends: $ => seq('EXTENDS', commaList1($.name)),

    unit: $ => choice(
        $.variable_declaration,
        $.constant_declaration,
        seq(optional("LOCAL"), $.operator_definition),
        seq(optional("LOCAL"), $.function_definition),
        seq(optional("LOCAL"), $.instance),
        seq(optional("LOCAL"), $.module_definition),
        $.assumption,
        $.theorem,
        $.module,
        $.single_line
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

    // Operator declaration (not definition)
    // Used, for example, when op accepts another op as parameter
    // op, op(_, _), _+_, etc.
    operator_declaration: $ => choice(
      $.identifier,
      seq($.identifier, '(', commaList1('_'), ')'),
      seq($.prefix_op, '_'),
      seq('_', $.infix_op, '_'),
      seq('_', $.postfix_op)
    ),

    // Operator definition
    // max(a, b) == IF a > b THEN a ELSE b
    // a \prec b == a.val < b.val
    operator_definition: $ => seq(
      choice(
        $.non_fix_lhs,
        seq($.prefix_op, $.identifier),
        seq($.identifier, $.infix_op, $.identifier),
        seq($.identifier, $.postfix_op)
      ),
      '==',
      $.expression
    ),

    // Named operator left-hand-side, with or without parameters
    // op, op(a, b)
    non_fix_lhs: $ => seq(
      $.identifier,
      optional(seq(
        '(',
        commaList1(choice($.identifier, $.operator_declaration)),
        ')'
      )),
    ),

    // f[x \in Nat] == 2*x
    function_definition: $ => seq(
      $.identifier,
      '[',
      commaList1($.quantifier_bound),
      ']',
      '==',
      $.expression
    ),

    // x, y, z \in S
    quantifier_bound: $ => seq(
      choice($.identifier_or_tuple, commaList1($.identifier)),
      '\\in',
      $.expression
    ),

    // A recursive parse rule for TLA+ expressions
    _expression: $ => choice(
      $.identifier,
      $._set_definition,
      $._set_operator,
      $._primitive_literal,
    ),

    // Ways of defining a new set.
    _set_definition: $ => choice(
      $.finite_set_literal,
      $.range_set_literal,
      $.set_map,
      $.set_filter
    ),

    // {1, 2, 3, 4, 5}
    finite_set_literal: $ => seq(
      '{',
      optional(
        seq(
          repeat(seq($._expression, ',')),
          $._expression
        )
      ),
      '}'
    ),

    // 0 .. 4
    range_set_literal: $ => prec.left(
      seq(
        $._expression,
        '..',
        $._expression
      )
    ),

    // { f[x, y] : x, y \in S }
    set_map: $ => seq(
      '{',
      $._expression,
      ':',
      $.multiple_named_elements_in,
      '}'
    ),

    // { x \in S : P(x) }
    set_filter: $ => seq(
      '{',
      $.single_named_element_in,
      ':',
      $._expression,
      '}'
    ),

    // Operators on sets
    _set_operator: $ => choice(
      $.set_membership,
      $.set_not_membership,
      $.set_union,
      $.set_intersection,
      $.set_subset,
      $.set_difference,
      $.set_powerset,
      $.set_flatten
    ),

    set_membership: $ => prec.left(seq($._expression, '\\in', $._expression)),
    set_not_membership: $ => prec.left(seq($._expression, '\\notin', $._expression)),
    set_union: $ => prec.left(seq($._expression, '\\cup', $._expression)),
    set_intersection: $ => prec.left(seq($._expression, '\\cap', $._expression)),
    set_subset: $ => prec.left(seq($._expression, '\\subseteq', $._expression)),
    set_difference: $ => prec.left(seq($._expression, '\\', $._expression)),
    set_powerset: $ => prec.left(seq('SUBSET', $._expression)),
    set_flatten: $ => prec.left(seq('UNION', $._expression)),

    // A single literal hardcoded value
    _primitive_literal: $ => choice(
      $.boolean_literal,
      $.integer_literal,
      $.real_literal,
      $.string_literal
    ),

    // TRUE, FALSE
    boolean_literal: $ => choice('TRUE', 'FALSE'),

    // x \in S
    single_named_element_in: $ => seq(
      $.identifier,
      '\\in',
      $._expression
    ),

    // x, y, z \in S
    multiple_named_elements_in: $ => seq(
      repeat(seq($.identifier, ',')),
      $.identifier,
      '\\in',
      $._expression
    ),

  }
});
