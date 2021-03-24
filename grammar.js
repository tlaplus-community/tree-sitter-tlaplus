function commaList1(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

function commaList(rule) {
  return optional(commaList1(rule))
}

module.exports = grammar({
  name: 'tlaplus',

  conflicts: $ => [
    [$.set_membership, $.set_membership],
    //[$.cross_product, $.cross_product]
  ],

  inline: $ => [
    $.expression
  ],

  rules: {
    source_file: $ => $.expression,

    expression: $ => choice(
      $.identifier,
      $.value,
      //$.set_membership,
      $.cross_product
    ),

    identifier: $ => /\w*[A-Za-z]\w*/,

    value: $ => /\d+/,

    set_membership: $ => seq(
      $.expression, '\\in', $.expression
    ),

    cross_product: $ => choice(
      $._cross_product_2,
      $._cross_product_3,
      $._cross_product_4,
      //$._cross_product_n
    ),

    _cross_product_2: $ => prec(4, seq($.expression, '\\X', $.expression)),

    _cross_product_3: $ => prec(5, seq($.expression, '\\X', $.expression, '\\X', $.expression)),

    _cross_product_4: $ => prec(10, seq($.expression, '\\X', $.expression, '\\X', $.expression, '\\X', $.expression)),

    _cross_product_n: $ => prec(6, seq(
      repeat1(seq($.expression, '\\X')),
      $.expression
    )),
  }
});
