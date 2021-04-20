const NL = /[\n\r]+/
const WS = /[\t ]+/

module.exports = grammar({
    name: 'test',

    conflicts: $ => [
      [$.list],
    ],

    rules: {

        source_file: $ => repeat(
            $._stmt,
        ),

        _stmt: $ => seq(
            $.list, optional(WS), ';'
        ),

        list: $ => seq(
            $.sel,
            repeat(seq(WS, $.sel))
        ),

        sel: $ => seq(
            optional('.'),
            $.id,
            repeat(seq('.', $.id))
        ),

        id: $ => /[a-zA-Z]+/

    }
});
