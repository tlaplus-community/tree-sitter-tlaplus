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
    source_file: $ => repeat1($.expression),

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
    name: $ => /\w*[A-Za-z]\w*/,

    // Identifier; should exclude reserved words
    identifier: $ => $.name,

    // <<x, y, z>>
    tuple_of_identifiers: $ => seq('<<', commaList1($.identifier), '>>'),

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
      choice(
        $.tuple_of_identifiers,
        commaList1($.identifier)
      ),
      '\\in',
      $.expression
    ),

    // INSTANCE ModuleName WITH x <- y, w <- z
    instance: $ => seq(
      'INSTANCE',
      $.name,
      optional(seq('WITH', commaList1($.substitution)))
    ),

    // x <- y, w <- z
    substitution: $ => seq(
      choice($.identifier, $.prefix_op, $.infix_op, $.postfix_op),
      '<-',
      $.argument
    ),

    // An argument given to an operator
    argument: $ => choice(
      $.expression,
      $.general_prefix_op,
      $.general_infix_op,
      $.general_postfix_op
    ),

    // Foo(x, y)!Bar(w, z)!...
    /*
    instance_prefix: $ => seq(
      $.identifier,
      optional(seq('(', commaList1($.expression), ')')),
      '!'
    ),
    */

    // Foo!bar
    general_identifier: $ => seq(
      //repeat($.instance_prefix), $.identifier
      $.identifier
    ),

    // Foo!\neg
    general_prefix_op: $ => seq(
      //repeat($.instance_prefix), $.prefix_op
      $.prefix_op
    ),

    // Foo!+
    general_infix_op: $ => seq(
      //repeat($.instance_prefix), $.infix_op
      $.infix_op
    ),

    // Foo!^#
    general_postfix_op: $ => seq(
      //repeat($.instance_prefix), $.postfix_op
      $.postfix_op
    ),

    // M == INSTANCE ModuleName
    module_definition: $ => seq(
      $.non_fix_lhs,
      '==',
      $.instance
    ),

    // ASSUME C \in Nat
    assumption: $ => seq(
      choice('ASSUME', 'ASSUMPTION', 'AXIOM'),
      $.expression
    ),

    // THEOREM Spec => []Safety
    theorem: $ => seq('THEOREM', $.expression),

    // Anything that evaluates to a value
    not_expression: $ => choice(
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
      $.function_definition,
      $.set_of_functions,
      $.record_definition,
      $.set_of_records,
      $.except,
      $.prev_func_val,
      $.tuple_literal,
      $.cross_product,
      $.stepexpression_or_stutter,
      $.stepexpression_no_stutter,
      $.fairness,
      $.if_then_else,
      $.case,
      $.let_in,
      $.conj,
      $.disj,
      $.number,
      $.string
    ),

    expression: $ => choice(
      $.set_membership,
      $.parentheses,
      $.bounded_quantification,
      $.unbounded_quantification,
      $.choose,
      $.finite_set_literal,
      $.set_filter,
      $.set_map,
      //$.function_evaluation,
      $.function_definition,
      $.set_of_functions,
      $.record_definition,
      $.set_of_records,
      $.except,
      $.prev_func_val,
      $.tuple_literal,
      //$.cross_product,
      $.stepexpression_or_stutter,
      $.stepexpression_no_stutter,
      $.fairness,
      $.if_then_else,
      $.case,
      //$.let_in,
      //$.conj,
      //$.disj,
      $.string,
      $.number,
    ),

    set_membership: $ => seq($.expression, '\\in', $.expression),

    // max(2, 3)
    bound_op: $ => seq($.general_identifier, '(', commaList1($.argument), ')'),

    // -5
    bound_prefix_op: $ => seq($.general_prefix_op, $.expression),

    // 3 + 5
    bound_infix_op: $ => seq($.expression, $.general_infix_op, $.expression),

    // x'
    bound_postfix_op: $ => seq($.expression, $.general_postfix_op),

    // ((a + b) + c)
    parentheses: $ => seq('(', $.expression, ')'),

    // \A x \in Nat : P(x)
    bounded_quantification: $ => seq(
      choice('\\A', '\\E'), commaList1($.quantifier_bound), ':', $.expression
    ),

    // \EE x : P(x)
    unbounded_quantification: $ => seq(
      choice('\\A', '\\E', '\\AA', '\\EE'), commaList1($.identifier), ':', $.expression
    ),

    // CHOOSE r \in Real : r >= 0
    choose: $ => seq(
      'CHOOSE',
      choice($.identifier, $.tuple_of_identifiers),
      optional(seq('\\in', $.expression)),
      ':',
      $.expression
    ),

    // {1, 2, 3, 4, 5}
    finite_set_literal: $ => seq('{', commaList($.expression), '}'),

    // { x \in S : P(x) }
    set_filter: $ => seq(
      '{',
      choice($.identifier, $.tuple_of_identifiers),
      '\\in',
      $.expression,
      ':',
      $.expression,
      '}'
    ),

    // { f[x, y] : x, y \in S }
    set_map: $ => seq(
      '{', $.expression, ':', commaList1($.quantifier_bound), '}'
    ),

    // f[5]
    function_evaluation: $ => seq(
      $.expression, '[', commaList1($.expression), ']'
    ),

    // [n \in Nat |-> 2*n]
    function_definition: $ => seq(
      '[', commaList1($.quantifier_bound), '|->', $.expression, ']'
    ),

    // [Nat -> Nat]
    set_of_functions: $ => seq(
      '[', $.expression, '->', $.expression, ']'
    ),

    // [foo |-> 0, bar |-> 1]
    record_definition: $ => seq(
      '[', commaList1(seq($.name, '|->', $.expression)), ']'
    ),

    // [foo : {0, 1}, bar : {0, 1}]
    set_of_records: $ => seq(
      '[', commaList1(seq($.name, ':', $.expression)), ']'
    ),

    // [f EXCEPT !.foo[bar].baz = 4, !.bar = 3]
    except: $ => seq(
      '[',
      $.expression,
      'EXCEPT',
      commaList1(
        seq(
          '!',
          repeat1(
            choice(
              seq('.', $.name),
              seq('[', commaList1($.expression), ']')
            )
          ),
          '=',
          $.expression
        )
      ),
      ']'
    ),

    // [f EXCEPT ![2] = @ + 1]
    prev_func_val: $ => '@',

    // <<1,2,3,4,5>>, <<>>
    tuple_literal: $ => seq('<<', commaList($.expression), '>>'),

    // S \X T \X P
    cross_product: $ => seq(
      $.expression, repeat1(seq(choice('\\X', '\\times'), $.expression))
    ),

    // [x ' > x]_<<x>>
    stepexpression_or_stutter: $ => seq(
      '[', $.expression, ']_', $.expression
    ),

    // <<x' > x>>_<<x>>
    stepexpression_no_stutter: $ => seq(
      '<<', $.expression, '>>_', $.expression
    ),

    // WF_vars(ActionName)
    fairness: $ => seq(
      choice('WF_', 'SF_'), $.expression, '(', $.expression, ')'
    ),

    // IF a > b THEN a ELSE b
    if_then_else: $ => seq(
      'IF', $.expression, 'THEN', $.expression, 'ELSE', $.expression
    ),

    // CASE x = 1 -> "1" [] x = 2 -> "2" [] OTHER -> "3"
    case: $ => prec.left(seq(
      'CASE', $.expression, '->', $.expression,
      repeat(seq('[]', $.expression, '->', $.expression)),
      optional(seq('[]', 'OTHER', '->', $.expression))
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
      $.expression
    ),

    // x /\ y
    conj: $ => repeat1(seq('/\\', $.expression)),

    // x \/ y
    disj: $ => repeat1(seq('\\/', $.expression)),

    // TRUE, FALSE
    boolean_literal: $ => choice('TRUE', 'FALSE'),
  }
});
