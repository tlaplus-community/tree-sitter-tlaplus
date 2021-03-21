function commaList1(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

function commaList(rule) {
  return optional(commaList1(rule))
}

module.exports = grammar({
  name: 'tlaplus',

  word: $ => $.identifier,

  rules: {
    source_file: $ => $.variable_decl_assign,

    variable_decl_assign: $ => seq(
      $.type,
      $.identifier,
      '=',
      $.value,
      ';'
    ),

    type: $ => choice(
      'int',
      'bool',
      'float',
      'double',
      'string'
    ),

    keyword: $ => choice(
      'IF', 'THEN', 'ELSE'
    ),

    identifier: $ => /\w*[A-Za-z]\w*/,

    value: $ => /\d+/,
  }
});
