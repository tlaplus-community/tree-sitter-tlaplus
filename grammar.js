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

        identifier: $ => /[a-zA-Z][\w]+/,

        _expr: $ => choice(
          $.number,
          $.identifier,
          $.parentheses,
          $.infix_op,
          $.conj_list,
          $.disj_list
        ),

        number: $ => /\d+/,

        parentheses: $ => seq(
          '(', $._expr, ')'
        ),

        infix_op: $ => choice(
          prec.left(1, seq($._expr, $.land, $._expr)),
          prec.left(1, seq($._expr, $.lor, $._expr)),
          prec.left(2, seq($._expr, $.add, $._expr)),
          prec.left(2, seq($._expr, $.subtract, $._expr)),
          prec.left(3, seq($._expr, $.multiply, $._expr)),
          prec.left(3, seq($._expr, $.divide, $._expr)),
        ),

        land: $ => choice('/\\', '∧'),
        lor: $ => choice('\\/', '∨'),
        add: $ => '+',
        subtract: $ => '-',
        multiply: $ => '*',
        divide: $ => '/',

        conj_list: $ => seq(
          $._indent, $.conj_item,
          repeat(seq($._newline, $.conj_item)),
          $._dedent
        ),

        conj_item: $ => seq($.land, $._expr),

        disj_list: $ => seq(
          $._indent, $.disj_item,
          repeat(seq($._newline, $.disj_item)),
          $._dedent
        ),

        disj_item: $ => seq($.lor, $._expr)
    }
});
