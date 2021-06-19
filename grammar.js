module.exports = grammar({
    name: 'tlaplus',

    externals: $ => [
      $._indent,
      $._newline,
      $._dedent,
    ],

    conflicts: $ => [
      //[$.conj_list]
    ],

    rules: {
        source_file: $ => repeat($.unit),

        unit: $ => seq(
          $.identifier, '==', $._expr
        ),

        identifier: $ => /[a-zA-Z]+/,

        _expr: $ => choice(
          $.number,
          $.identifier,
          $.parentheses,
          $.infix_op,
          $.conj_list
        ),

        number: $ => /\d+/,

        parentheses: $ => seq(
          '(', $._expr, ')'
        ),

        infix_op: $ => choice(
          prec.left(1, seq($._expr, $.land, $._expr)),
          prec.left(2, seq($._expr, $.add, $._expr)),
          prec.left(3, seq($._expr, $.multiply, $._expr)),
        ),

        land: $ => choice('/\\', '∧'),
        add: $ => '+',
        multiply: $ => '*',

        conj_list: $ => seq(
          $._indent, $.conj_item,
          repeat(seq($._newline, $.conj_item)),
          $._dedent
        ),

        conj_item: $ => seq($.land, $._expr)
    }
});
