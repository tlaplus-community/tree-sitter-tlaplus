// A sequence of one or more comma-separated strings matching the rule
function commaList1(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

// A sequence of zero or more comma-separated strings matching the rule
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
      $._expression
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
      $._expression
    ),

    // x, y, z \in S
    quantifier_bound: $ => seq(
      choice($.identifier_or_tuple, commaList1($.identifier)),
      '\\in',
      $._expression
    ),

    // INSTANCE ModuleName WITH x <- y, w <- z
    instance: $ => seq(
      'INSTANCE',
      $.name,
      optional(seq('WITH'), commaList1($.substitution))
    ),

    // x <- y, w <- z
    substitution: $ => seq(
      choice($.identifier, $.prefix_op, $.infix_op, $.postfix_op),
      '<-',
      $.argument
    ),

    argument: $ => choice(
      $._expression,
      $.general_prefix_op,
      $.general_infix_op,
      $.general_postfix_op
    ),

    // Foo(x, y)!Bar(w, z)!...
    instance_prefix: $ => repeat(
      $.identifier,
      optional(seq('(', commaList1($._expression), ')')),
      '!'
    ),

    // Foo!bar
    general_identifier: $ => seq($.instance_prefix, $.identifier),

    // Foo!\neg
    general_prefix_op: $ => seq($.instance_prefix, $.prefix_op),

    // Foo!+
    general_infix_op: $ => seq($.instance_prefix, $.infix_op),

    // Foo!^#
    general_postfix_op: $ => seq($.instance_prefix, $.postfix_op),

    // M == INSTANCE ModuleName
    module_definition: $ => seq(
      $.non_fix_lhs,
      '==',
      $.instance
    ),

    // ASSUME C \in Nat
    assumption: $ => seq(
      choice('ASSUME', 'ASSUMPTION', 'AXIOM'),
      $._expression
    ),

    // THEOREM Spec => []Safety
    theorem: $ => seq('THEOREM', $._expression),

    // Anything that evaluates to a value
    _expression: $ => choice(
      $.general_identifier,
      seq($.general_identifier, '(', commaList1($.argument), ')'),
      seq($.general_prefix_op, $._expression),
      seq($._expression, $.general_infix_op, $._expression),
      seq($._expression, $.general_postfix_op),
      seq('(', $._expression, ')'),
      seq(choice('\\A', '\\E'), commaList1($.quantifier_bound), ':', $._expression),
      seq(choice('\\A', '\\E', '\\AA', '\\EE'), commaList1($.identifier), ':', $._expression),
      $.choose,
      $.finite_set_literal,
      $.set_filter,
      $.set_map,
      $.function_evaluation,
      $.function_definition,
      $.set_of_functions,
      $.record_definition,
      $.set_of_records,
      $.except,
      $.prev_func_val,
      $.tuple_literal,
      $.cross_product,
      $.step_expression_or_stutter,
      $.step_expression_no_stutter,
      $.fairness,
      $.if_then_else,
      $.case,
      $.let_in,
      $.conj,
      $.disj,
      $.number,
      $.string
    ),

    // CHOOSE r \in Real : r >= 0
    choose: $ => seq(
      'CHOOSE',
      $.identifier_or_tuple,
      optional(seq('\\in', $._expression)),
      ':',
      $._expression
    ),

    // {1, 2, 3, 4, 5}
    finite_set_literal: $ => seq('{', commaList($._expression), '}'),

    // { x \in S : P(x) }
    set_filter: $ => seq(
      '{', $.identifier_or_tuple, '\\in', $._expression, ':', $._expression, '}'
    ),

    // { f[x, y] : x, y \in S }
    set_map: $ => seq(
      '{', $._expression, ':', commaList1($.quantifier_bound), '}'
    ),

    // f[5]
    function_evaluation: $ => seq(
      $._expression, '[', commaList1($._expression), ']'
    ),

    // [n \in Nat |-> 2*n]
    function_definition: $ => seq(
      '[', commaList1($.quantifier_bound), '|->', $._expression, ']'
    ),

    // [Nat -> Nat]
    set_of_functions: $ => seq(
      '[', $._expression, '->', $._expression, ']'
    ),

    // [foo |-> 0, bar |-> 1]
    record_definition: $ => seq(
      '[', commaList1(seq($.name, '|->', $._expression)), ']'
    ),

    // [foo : {0, 1}, bar : {0, 1}]
    set_of_records: $ => seq(
      '[', commaList1(seq($.name, ':', $._expression)), ']'
    ),

    // [f EXCEPT !.foo[bar].baz = 4, !.bar = 3]
    except: $ => seq(
      '[',
      $._expression,
      'EXCEPT',
      commaList1(
        seq(
          '!',
          repeat1(
            choice(
              seq('.', $.name),
              seq('[', commaList1($._expression), ']')
            )
          ),
          '=',
          $._expression
        )
      ),
      ']'
    ),

    // [f EXCEPT ![2] = @ + 1]
    prev_func_val: $ => '@',

    // <<1,2,3,4,5>>, <<>>
    tuple_literal: $ => seq('<<', commaList($._expression), '>>'),

    // S \X T \X P
    cross_product: $ => seq(
      $._expression, repeat1(choice('\\X', '\\times'), $._expression)
    ),

    // [x ' > x]_<<x>>
    step_expression_or_stutter: $ => seq(
      '[', $._expression, ']_', $._expression
    ),

    // <<x' > x>>_<<x>>
    step_expression_no_stutter: $ => seq(
      '<<', $._expression, '>>_', $._expression
    ),

    // WF_vars(ActionName)
    fairness: $ => seq(
      choice('WF_', 'SF_'), $._expression, '(', $._expression, ')'
    ),

    // IF a > b THEN a ELSE b
    if_then_else: $ => seq(
      'IF', $._expression, 'THEN', $._expression, 'ELSE', $._expression
    ),

    // CASE x = 1 -> "1" [] x = 2 -> "2" [] OTHER -> "3"
    case: $ => seq(
      'CASE', $._expression, '->', $._expression,
      repeat('[]', $._expression, '->', $._expression),
      optional('[]', 'OTHER', '->', $._expression)
    ),

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
      $._expression
    ),

    // x /\ y
    conj: $ => repeat1(seq('/\\', $._expression)),

    // x \/ y
    disj: $ => repeat1(seq('\\/', $._expression)),

    // TRUE, FALSE
    boolean_literal: $ => choice('TRUE', 'FALSE'),
  }
});
