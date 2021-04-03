function commaList1(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

function commaList(rule) {
  return optional(commaList1(rule))
}

module.exports = grammar({
  name: 'tlaplus',

  conflicts: $ => [
    //[$.set_membership, $.set_membership],
    //[$.cross_product, $.cross_product],
    //[$.cross_product, $.set_union]
  ],

  inline: $ => [
    $.expression
  ],

  rules: {
    source_file: $ => $.expression,

    expression: $ => choice(
      prec(1, $.identifier),
      $.value,
      //$.cross_product,
      $.parenthesis,
      $.set_union,
      $.subseteq,
    ),

    //set_union: $ => prec.dynamic(-2, prec.left(8, seq($.expression, '\\cup', $.expression))),
    set_union: $ => prec.left(8, seq($.expression, '\\cup', $.expression)),

    subseteq: $ => prec(5, seq($.expression, '\\subseteq', $.expression)),

    identifier: $ => /\w*[A-Za-z]\w*/,

    parenthesis: $ => seq('(', $.expression, ')'),

    value: $ => /\d+/,

    cross_product: $ => prec.dynamic(-1, seq(
      repeat1(seq($.expression, '\\X')),
      $.expression
    )),
  }
});
