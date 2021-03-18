module.exports = grammar({
  name: 'tlaplus',

  rules: {
    source_file: $ => repeat1($.module),

    module: $ => seq(
        $.single_line,
        'MODULE',
        $.identifier,
        $.single_line,
        optional($.extends),
        repeat($.module_content),
        $.double_line
    ),

    extends: $ => seq(
        'EXTENDS',
        repeat(seq($.identifier, ',')),
        $.identifier
    ),

    module_content: $ => choice(
        $.constants,
        $.variables,
        $.definition,
        $.macro,
    ),

    constants: $ => seq(
        choice('CONSTANT', 'CONSTANTS'),
        repeat(seq($.identifier, ',')),
        $.identifier
    ),

    variables: $ => seq(
      choice('VARIABLE', 'VARIABLES'),
        repeat(seq($.identifier, ',')),
        $.identifier
    ),

    definition: $ => seq(
      $.identifier,
      '==',
      $._expression
    ),

    macro: $ => seq(
      $.identifier,
      '(',
      repeat(seq($.identifier, ',')),
      $.identifier,
      ')',
      '==',
      $._expression
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

    // 1, 42, -128, etc.
    integer_literal: $ => /\-?\d+/,

    // 3.14159, 2, -3.5, etc.
    real_literal: $ => /\-?\d+(\.\d+)?/,

    // "foobar", "", etc.
    string_literal: $ => /\".*\"/,

    // Line of --------- of length at least 4
    single_line: $ => seq('-', '-', '-', '-', repeat('-')),

    // Line of =========== of length at least 4
    double_line: $ => seq('=', '=', '=', '=', repeat('=')),

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

    // Name (module, definition, etc.)
    identifier: $ => /[A-Za-z0-9_]+/,
  }
});
