module.exports = grammar({
    name: 'tlaplus',

    externals: $ => [
      $.conj_bullet,
      $.indent,
      $.dedent,
      $.newline,
    ],

    conflicts: $ => [
      [$.conj_list]
    ],

    rules: {
        source_file: $ => repeat($.unit),

        unit: $ => seq(
          $.identifier, '==', $._expr
        ),

        identifier: $ => /\w+/,

        _expr: $ => choice(
          $.number,
          $.infix_op,
          $.conj_list
        ),

        number: $ => /\d+/,

        infix_op: $ => choice(
          prec.left(1, seq($._expr, $.land, $._expr)),
          prec.left(2, seq($._expr, $.add, $._expr)),
          prec.left(3, seq($._expr, $.multiply, $._expr)),
        ),

        land: $ => choice('/\\', '∧'),
        add: $ => '+',
        multiply: $ => '*',

        conj_list: $ => seq(
          $.indent, $.conj_bullet, $._expr,
          repeat(seq($.newline, $.indent, $.conj_bullet, $._expr))
        ),
    }
});
