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

  conflicts: $ => [
    [$.general_identifier, $.tuple_of_identifiers]
  ],

  rules: {
    source_file: $ => repeat1($._expr),

    reserved_word: $ => choice(
      'ASSUME',       'ELSE',       'LOCAL',      'UNION',
      'ASSUMPTION',   'ENABLED',    'MODULE',     'VARIABLE',
      'AXIOM',        'EXCEPT',     'OTHER',      'VARIABLES',
      'CASE',         'EXTENDS',    'SF_',        'WF_',
      'CHOOSE',       'IF',         'SUBSET',     'WITH',
      'CONSTANT',     'IN',         'THEN',
      'CONSTANTS',    'INSTANCE',   'THEOREM',    'COROLLARY',
      'DOMAIN',       'LET',        'UNCHANGED',
      'BY',           'HAVE',       'QED',        'TAKE',
      'DEF',          'HIDE',       'RECURSIVE',  'USE',
      'DEFINE',       'PROOF',      'WITNESS',    'PICK',
      'DEFS',         'PROVE',      'SUFFICES',   'NEW',
      'LAMBDA',       'STATE',      'ACTION',     'TEMPORAL',
      'OBVIOUS',      'OMITTED',    'LEMMA',      'PROPOSITION',
      'ONLY'
    ),

    // Name (module, definition, etc.)
    // Can contain letters, numbers, and underscores
    // If only one character long, must be letter (not number or _)
    name: $ => /\w*[A-Za-z]\w*/,

    // Identifier; should exclude reserved words
    identifier: $ => $.name,

    // <<x, y, z>>
    tuple_of_identifiers: $ => seq(
      $.langle_bracket,
      commaList1($.identifier),
      $.rangle_bracket
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

    // TRUE, FALSE, BOOLEAN
    boolean: $ => choice('TRUE', 'FALSE', 'BOOLEAN'),

    // Various syntactic elements and their unicode equivalents
    def_eq:           $ => choice('==', '≜'),
    set_in:           $ => choice('\\in', '∈'),
    gets:             $ => choice('<-', '⟵'),
    forall:           $ => choice('\\A', '\\forall', '∀'),
    exists:           $ => choice('\\E', '\\exists', '∃'),
    temporal_forall:  $ => choice('\\AA'),
    temporal_exists:  $ => choice('\\EE'),
    all_map_to:       $ => choice('|->', '⟼', '↦'),
    maps_to:          $ => choice('->', '⟶'),
    langle_bracket:   $ => choice('<<', '〈'),
    rangle_bracket:   $ => choice('>>', '〉'),
    case_box:         $ => choice('[]', '□'),
    case_arrow:       $ => choice('->', '⟶'),
    bullet_conj:      $ => choice('/\\', '∧'),
    bullet_disj:      $ => choice('\\/', '∨'),

    // Prefix operator symbols and their unicode equivalents
    lnot:             $ => choice('\\lnot', '\\neg', '~', '¬'),
    union:            $ => 'UNION',
    subset:           $ => 'SUBSET',
    domain:           $ => 'DOMAIN',
    negative:         $ => '-',
    enabled:          $ => 'ENABLED',
    unchanged:        $ => 'UNCHANGED',
    always:           $ => choice('[]', '□'),
    eventually:       $ => choice('<>', '⋄'),

    // Infix operator symbols and their unicode equivalents
    implies:          $ => choice('=>', '⟹'),
    plus_arrow:       $ => choice('-+->', '⇸'),
    equiv:            $ => choice('\\equiv', '≡'),
    iff:              $ => choice('<=>', '⟺'),
    leads_to:         $ => choice('~>', '⇝'),
    land:             $ => choice('/\\', '\\land', '∧'),
    lor:              $ => choice('\\/', '\\lor', '∨'),
    assign:           $ => choice(':=', '≔'),
    bnf_rule:         $ => choice('::=', '⩴'),
    eq:               $ => '=',
    neq:              $ => choice('/=', '#', '≠'),
    lt:               $ => '<',
    gt:               $ => '>',
    leq:              $ => choice('<=', '\\leq', '≤'),
    geq:              $ => choice('>=', '\\geq', '≥'),
    approx:           $ => choice('\\approx', '≈'),
    rs_ttile:         $ => choice('|-', '⊢'),
    rd_ttile:         $ => choice('|=', '⊨'),
    ls_ttile:         $ => choice('-|', '⊣'),
    ld_ttile:         $ => choice('=|', '⫤'),
    asymp:            $ => choice('\\asymp', '≍'),
    cong:             $ => choice('\\cong', '≅'),
    doteq:            $ => choice('\\doteq', '≐'),
    gg:               $ => choice('\\gg', '≫'),
    ll:               $ => choice('\\ll', '≪'),
    in:               $ => choice('\\in', '∈'),
    notin:            $ => choice('\\notin', '∉'),
    prec:             $ => choice('\\prec', '≺'),
    succ:             $ => choice('\\succ', '≻'),
    preceq:           $ => choice('\\preceq', '⪯'),
    succeq:           $ => choice('\\succeq', '⪰'),
    propto:           $ => choice('\\propto', '∝'),
    sim:              $ => choice('\\sim', '∼'),
    simeq:            $ => choice('\\simeq', '≃'),
    sqsubset:         $ => choice('\\sqsubset', '⊏'),
    sqsupset:         $ => choice('\\sqsupset', '⊐'),
    sqsubseteq:       $ => choice('\\sqsubseteq', '⊑'),
    sqsupseteq:       $ => choice('\\sqsupseteq', '⊒'),
    subset:           $ => choice('\\subset', '⊂'),
    supset:           $ => choice('\\supset', '⊃'),
    subseteq:         $ => choice('\\subseteq', '⊆'),
    supseteq:         $ => choice('\\supseteq', '⊇'),
    compose:          $ => '@@',
    map_to:           $ => ':>',
    map_from:         $ => '<:',
    setminus:         $ => '\\',
    cap:              $ => choice('\\cap', '∩'),
    cup:              $ => choice('\\cup', '∪'),
    dots_2:           $ => choice('..', '‥'),
    dots_3:           $ => choice('...', '…'),
    plus:             $ => '+',
    plusplus:         $ => '++',
    oplus:            $ => choice('\\oplus', '⊕'),
    ominus:           $ => choice('\\ominus', '⊖'),
    mod:              $ => '%',
    modmod:           $ => '%%',
    vert:             $ => '|',
    vertvert:         $ => choice('||', '‖'),
    minus:            $ => '-',
    minusminus:       $ => '--',
    amp:              $ => '&',
    ampamp:           $ => '&&',
    odot:             $ => choice('\\odot', '⊙'),
    oslash:           $ => choice('\\oslash', '⊘'),
    otimes:           $ => choice('\\otimes', '⊗'),
    mul:              $ => '*',
    mulmul:           $ => '**',
    slash:            $ => '/',
    slashslash:       $ => '//',
    bigcirc:          $ => choice('\\bigcirc', '◯'),
    bullet:           $ => choice('\\bullet', '●'),
    div:              $ => choice('\\div', '÷'),
    circ:             $ => choice('\\circ', '∘'),
    star:             $ => choice('\\star', '⋆'),
    excl:             $ => choice('!!', '‼'),
    qq:               $ => choice('??', '⁇'),
    hashhash:         $ => '##',
    dol:              $ => '$',
    doldol:           $ => '$$',
    sqcap:            $ => choice('\\sqcap', '⊓'),
    sqcup:            $ => choice('\\sqcup', '⊔'),
    uplus:            $ => choice('\\uplus', '⊎'),
    times:            $ => choice('\\X', '\\times', '×'),
    wr:               $ => choice('\\wr', '≀'),
    cdot:             $ => choice('\\cdot', '⋅'),
    pow:              $ => '^',
    powpow:           $ => '^^',
    rfield:           $ => '.',

    // All prefix operator symbols
    prefix_op_symbol: $ => choice(
      $.lnot,     $.union,      $.subset,     $.domain,     $.negative,
      $.enabled,  $.unchanged,  $.always,     $.eventually
    ),

    // All prefix operators
    prefix_op: $ => choice(
      $.prefix_op_lnot,       $.prefix_op_union,    $.prefix_op_subset,
      $.prefix_op_domain,     $.prefix_op_negative, $.prefix_op_enabled,
      $.prefix_op_unchanged,  $.prefix_op_always,   $.prefix_op_eventually
    ),

    // Prefix operators are given highest value in precedence range
    prefix_op_lnot:       $ => prec(4, seq($.lnot, $._expr)),
    prefix_op_union:      $ => prec(8, seq($.union, $._expr)),
    prefix_op_subset:     $ => prec(8, seq($.subset, $._expr)),
    prefix_op_domain:     $ => prec(9, seq($.domain, $._expr)),
    prefix_op_negative:   $ => prec(12, seq($.negative, $._expr)),
    prefix_op_enabled:    $ => prec(15, seq($.enabled, $._expr)),
    prefix_op_unchanged:  $ => prec(15, seq($.unchanged, $._expr)),
    prefix_op_always:     $ => prec(15, seq($.always, $._expr)),
    prefix_op_eventually: $ => prec(15, seq($.eventually, $._expr)),

    // All infix operator symbols
    infix_op_symbol: $ => choice(
      $.implies,      $.plus_arrow,     $.equiv,        $.iff,
      $.leads_to,     $.land,           $.lor,          $.assign,
      $.bnf_rule,     $.eq,             $.neq,          $.lt,
      $.gt,           $.leq,            $.geq,          $.approx,
      $.rs_ttile,     $.rd_ttile,       $.ls_ttile,     $.ld_ttile,
      $.asymp,        $.cong,           $.doteq,        $.gg,
      $.ll,           $.in,             $.notin,        $.prec,
      $.succ,         $.preceq,         $.succeq,       $.sim,
      $.simeq,        $.sqsubset,       $.sqsupset,     $.sqsubseteq,
      $.sqsupseteq,   $.compose,        $.map_to,       $.map_from,
      $.setminus,     $.cap,            $.cup,          $.dots_2,
      $.dots_3,       $.plus,           $.plusplus,     $.oplus,
      $.ominus,       $.mod,            $.modmod,       $.vert,
      $.vertvert,     $.minus,          $.minusminus,   $.amp,
      $.ampamp,       $.odot,           $.oslash,       $.otimes,
      $.mul,          $.mulmul,         $.slash,        $.slashslash,
      $.bigcirc,      $.bullet,         $.div,          $.circ,
      $.star,         $.excl,           $.hashhash,     $.dol,
      $.doldol,       $.qq,             $.sqcap,        $.sqcup,
      $.uplus,        $.wr,             $.cdot,         $.pow,
      $.powpow,       $.rfield
    ),

    // All infix operators
    infix_op: $ => choice(
      $.infix_op_implies,     $.infix_op_plus_arrow,      $.infix_op_equiv,
      $.infix_op_iff,         $.infix_op_leads_to,        $.infix_op_land,
      $.infix_op_lor,         $.infix_op_assign,          $.infix_op_bnf_rule,
      $.infix_op_eq,          $.infix_op_neq,             $.infix_op_lt,
      $.infix_op_gt,          $.infix_op_leq,             $.infix_op_geq,
      $.infix_op_approx,      $.infix_op_rs_ttile,        $.infix_op_rd_ttile,
      $.infix_op_ls_ttile,    $.infix_op_ld_ttile,        $.infix_op_asymp,
      $.infix_op_cong,        $.infix_op_doteq,           $.infix_op_gg,
      $.infix_op_ll,          $.infix_op_in,              $.infix_op_notin,
      $.infix_op_prec,        $.infix_op_succ,            $.infix_op_preceq,
      $.infix_op_succeq,      $.infix_op_sim,             $.infix_op_simeq,
      $.infix_op_sqsubset,    $.infix_op_sqsupset,        $.infix_op_sqsubseteq,
      $.infix_op_sqsupseteq,  $.infix_op_subset,          $.infix_op_supset,
      $.infix_op_subseteq,    $.infix_op_supseteq,        $.infix_op_compose,
      $.infix_op_map_to,      $.infix_op_map_from,        $.infix_op_setminus,
      $.infix_op_cap,         $.infix_op_cup,             $.infix_op_2dots,
      $.infix_op_3dots,       $.infix_op_plus,            $.infix_op_plusplus,
      $.infix_op_oplus,       $.infix_op_ominus,          $.infix_op_mod,
      $.infix_op_modmod,      $.infix_op_vert,            $.infix_op_vertvert,
      $.infix_op_minus,       $.infix_op_minusminus,      $.infix_op_amp,
      $.infix_op_ampamp,      $.infix_op_odot,            $.infix_op_oslash,
      $.infix_op_otimes,      $.infix_op_mul,             $.infix_op_mulmul,
      $.infix_op_slash,       $.infix_op_slashslash,      $.infix_op_bigcirc,
      $.infix_op_bullet,      $.infix_op_div,             $.infix_op_circ,
      $.infix_op_star,        $.infix_op_excl,            $.infix_op_hashhash,
      $.infix_op_dol,         $.infix_op_doldol,          $.infix_op_qq,
      $.infix_op_sqcap,       $.infix_op_sqcup,           $.infix_op_uplus,
      $.infix_op_wr,          $.infix_op_cdot,            $.infix_op_pow,
      $.infix_op_powpow,      $.infix_op_rfield
    ),

    // Infix operators are given highest value in precedence range for parsing
    // Infix operators are all marked as left-associative for parsing purposes
    // Operator precedence range & associativity conflicts must be enforced
    // on semantic level
    infix_op_implies:     $ => prec.left(1, seq($._expr, $.implies, $._expr)),
    infix_op_plus_arrow:  $ => prec.left(2, seq($._expr, $.plus_arrow, $._expr)),
    infix_op_equiv:       $ => prec.left(2, choice('\\equiv', '≡')),
    infix_op_iff:         $ => prec.left(2, choice('<=>', '⟺')),
    infix_op_leads_to:    $ => prec.left(2, choice('~>', '⇝')),
    infix_op_land:        $ => prec.left(3, choice('/\\', '\\land', '∧')),
    infix_op_lor:         $ => prec.left(3, choice('\\/', '\\lor', '∨')),
    infix_op_assign:      $ => prec.left(5, ':='),
    infix_op_bnf_rule:    $ => prec.left(5, '::='),
    infix_op_eq:          $ => prec.left(5, '='),
    infix_op_neq:         $ => prec.left(5, choice('/=', '#', '≠')),
    infix_op_lt:          $ => prec.left(5, '<'),
    infix_op_gt:          $ => prec.left(5, '>'),
    infix_op_leq:         $ => prec.left(5, choice('<=', '\\leq', '≤')),
    infix_op_geq:         $ => prec.left(5, choice('>=', '\\geq', '≥')),
    infix_op_approx:      $ => prec.left(5, choice('\\approx', '≈')),
    infix_op_rs_ttile:    $ => prec.left(5, choice('|-', '⊢')),
    infix_op_rd_ttile:    $ => prec.left(5, choice('|=', '⊨')),
    infix_op_ls_ttile:    $ => prec.left(5, choice('-|', '⊣')),
    infix_op_ld_ttile:    $ => prec.left(5, choice('=|', '⫤')),
    infix_op_asymp:       $ => prec.left(5, choice('\\asymp', '≍')),
    infix_op_cong:        $ => prec.left(5, choice('\\cong', '≅')),
    infix_op_doteq:       $ => prec.left(5, choice('\\doteq', '≐')),
    infix_op_gg:          $ => prec.left(5, choice('\\gg', '≫')),
    infix_op_ll:          $ => prec.left(5, choice('\\ll', '≪')),
    infix_op_in:          $ => prec.left(5, choice('\\in', '∈')),
    infix_op_notin:       $ => prec.left(5, choice('\\notin', '∉')),
    infix_op_prec:        $ => prec.left(5, choice('\\prec', '≺')),
    infix_op_succ:        $ => prec.left(5, choice('\\succ', '≻')),
    infix_op_preceq:      $ => prec.left(5, choice('\\preceq', '⪯')),
    infix_op_succeq:      $ => prec.left(5, choice('\\succeq', '⪰')),
    infix_op_propto:      $ => prec.left(5, choice('\\propto', '∝')),
    infix_op_sim:         $ => prec.left(5, choice('\\sim', '∼')),
    infix_op_simeq:       $ => prec.left(5, choice('\\simeq', '≃')),
    infix_op_sqsubset:    $ => prec.left(5, choice('\\sqsubset', '⊏')),
    infix_op_sqsupset:    $ => prec.left(5, choice('\\sqsupset', '⊐')),
    infix_op_sqsubseteq:  $ => prec.left(5, choice('\\sqsubseteq', '⊑')),
    infix_op_sqsupseteq:  $ => prec.left(5, choice('\\sqsupseteq', '⊒')),
    infix_op_subset:      $ => prec.left(5, choice('\\subset', '⊂')),
    infix_op_supset:      $ => prec.left(5, choice('\\supset', '⊃')),
    infix_op_subseteq:    $ => prec.left(5, choice('\\subseteq', '⊆')),
    infix_op_supseteq:    $ => prec.left(5, choice('\\supseteq', '⊇')),
    infix_op_compose:     $ => prec.left(6, '@@'),
    infix_op_map_to:      $ => prec.left(7, ':>'),
    infix_op_map_from:    $ => prec.left(7, '<:'),
    infix_op_setminus:    $ => prec.left(8, '\\'),
    infix_op_cap:         $ => prec.left(8, choice('\\cap', '∩')),
    infix_op_cup:         $ => prec.left(8, choice('\\cup', '∪')),
    infix_op_2dots:       $ => prec.left(9, '..'),
    infix_op_3dots:       $ => prec.left(9, choice('...', '…')),
    infix_op_plus:        $ => prec.left(10, '+'),
    infix_op_plusplus:    $ => prec.left(10, '++'),
    infix_op_oplus:       $ => prec.left(10, choice('\\oplus', '⊕')),
    infix_op_ominus:      $ => prec.left(11, choice('\\ominus', '⊖')),
    infix_op_mod:         $ => prec.left(11, '%'),
    infix_op_modmod:      $ => prec.left(11, '%%'),
    infix_op_vert:        $ => prec.left(11, '|'),
    infix_op_vertvert:    $ => prec.left(11, choice('||', '‖')),
    infix_op_minus:       $ => prec.left(11, '-'),
    infix_op_minusminus:  $ => prec.left(11, '--'),
    infix_op_amp:         $ => prec.left(13, '&'),
    infix_op_ampamp:      $ => prec.left(13, '&&'),
    infix_op_odot:        $ => prec.left(13, choice('\\odot', '⊙')),
    infix_op_oslash:      $ => prec.left(13, choice('\\oslash', '⊘')),
    infix_op_otimes:      $ => prec.left(13, choice('\\otimes', '⊗')),
    infix_op_mul:         $ => prec.left(13, '*'),
    infix_op_mulmul:      $ => prec.left(13, '**'),
    infix_op_slash:       $ => prec.left(13, '/'),
    infix_op_slashslash:  $ => prec.left(13, '//'),
    infix_op_bigcirc:     $ => prec.left(13, choice('\\bigcirc', '◯')),
    infix_op_bullet:      $ => prec.left(13, choice('\\bullet', '●')),
    infix_op_div:         $ => prec.left(13, choice('\\div', '÷')),
    infix_op_circ:        $ => prec.left(13, choice('\\circ', '∘')),
    infix_op_star:        $ => prec.left(13, choice('\\star', '⋆')),
    infix_op_excl:        $ => prec.left(13, choice('!!', '‼')),
    infix_op_hashhash:    $ => prec.left(13, '##'),
    infix_op_dol:         $ => prec.left(13, '$'),
    infix_op_doldol:      $ => prec.left(13, '$$'),
    infix_op_qq:          $ => prec.left(13, '??'),
    infix_op_sqcap:       $ => prec.left(13, choice('\\sqcap', '⊓')),
    infix_op_sqcup:       $ => prec.left(13, choice('\\sqcup', '⊔')),
    infix_op_uplus:       $ => prec.left(13, choice('\\uplus', '⊎')),
    infix_op_times:       $ => prec.left(13, choice('\\X', '\\times', '×')),
    infix_op_wr:          $ => prec.left(14, choice('\\wr', '≀')),
    infix_op_cdot:        $ => prec.left(14, choice('\\cdot', '⋅')),
    infix_op_pow:         $ => prec.left(14, '^'),
    infix_op_powpow:      $ => prec.left(14, '^^'),
    infix_op_rfield:      $ => prec.left(17, '.'),

    // All postfix operators
    postfix_op: $ => choice(
      $.postfix_op_plus,    $.postfix_op_ast,
      $.postfix_op_hash,    $.postfix_op_prime
    ),

    // Postfix operators are given highest value in precedence range
    postfix_op_plus:  $ => prec(15, choice('^+', '⁺')),
    postfix_op_ast:   $ => prec(15, '^*'),
    postfix_op_hash:  $ => prec(15, '^#'),
    postfix_op_prime: $ => prec(15, '\''),

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
        $.recursive_operator_declaration,
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

    // RECURSIVE op(_, _)
    recursive_operator_declaration: $ => seq(
      'RECURSIVE', commaList1($.operator_declaration)
    ),

    // Operator declaration (not definition)
    // Used, for example, when op accepts another op as parameter
    // op, op(_, _), _+_, etc.
    operator_declaration: $ => choice(
      $.identifier,
      seq($.identifier, '(', commaList1('_'), ')'),
      seq($.prefix_op_symbol, '_'),
      seq('_', $.infix_op_symbol, '_'),
      seq('_', $.postfix_op)
    ),

    // Operator definition
    // max(a, b) == IF a > b THEN a ELSE b
    // a \prec b == a.val < b.val
    // x ≜ 〈 1, 2, 3, 4, 5 〉
    operator_definition: $ => seq(
      choice(
        $.non_fix_lhs,
        seq($.prefix_op_symbol, $.identifier),
        seq($.identifier, $.infix_op_symbol, $.identifier),
        seq($.identifier, $.postfix_op)
      ),
      $.def_eq,
      $._expr
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
      $.def_eq,
      $._expr
    ),

    // x, y, z \in S
    quantifier_bound: $ => seq(
      choice(
        $.tuple_of_identifiers,
        commaList1($.identifier)
      ),
      $.set_in,
      $._expr
    ),

    // INSTANCE ModuleName WITH x <- y, w <- z
    instance: $ => seq(
      'INSTANCE',
      $.name,
      optional(seq('WITH', commaList1($.substitution)))
    ),

    // x <- y, w <- z
    substitution: $ => seq(
      choice($.identifier, $.prefix_op_symbol, $.infix_op_symbol, $.postfix_op),
      $.gets,
      $.argument
    ),

    // An argument given to an operator
    argument: $ => choice(
      $._expr,
      $.general_prefix_op,
      $.general_infix_op,
      $.general_postfix_op
    ),

    // Foo(x, y)!Bar(w, z)!...
    instance_prefix: $ => seq(
      $.identifier,
      optional(seq('(', commaList1($._expr), ')')),
      '!'
    ),

    // Foo!bar
    general_identifier: $ => seq(
      //repeat($.instance_prefix), $.identifier
      $.identifier
    ),

    // Foo!\neg
    general_prefix_op: $ => seq(
      //repeat($.instance_prefix), $.prefix_op
      $.prefix_op_symbol
    ),

    // Foo!+
    general_infix_op: $ => seq(
      //repeat($.instance_prefix), $.infix_op
      $.infix_op_symbol
    ),

    // Foo!^#
    general_postfix_op: $ => seq(
      //repeat($.instance_prefix), $.postfix_op
      $.postfix_op
    ),

    // M == INSTANCE ModuleName
    module_definition: $ => seq(
      $.non_fix_lhs,
      $.def_eq,
      $.instance
    ),

    // ASSUME C \in Nat
    assumption: $ => seq(
      choice('ASSUME', 'ASSUMPTION', 'AXIOM'),
      $._expr
    ),

    // THEOREM Spec => []Safety
    theorem: $ => seq('THEOREM', $._expr),

    // Anything that evaluates to a value
    _expr: $ => choice(
      $.general_identifier,
      //$.bound_op,
      //$.bound_prefix_op,
      //$.bound_infix_op,
      //$.bound_postfix_op,
      $.parentheses,
      $.bounded_quantification,
      $.unbounded_quantification,
      $.choose,
      $.finite_set_literal,
      $.set_filter,
      $.set_map,
      $.function_evaluation,
      $.function_value,
      $.set_of_functions,
      $.record_value,
      $.set_of_records,
      $.except,
      $.prev_func_val,
      $.tuple_literal,
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
      $.boolean
    ),

    // max(2, 3)
    bound_op: $ => seq($.general_identifier, '(', commaList1($.argument), ')'),

    // -5
    bound_prefix_op: $ => seq($.general_prefix_op, $._expr),

    // 3 + 5
    bound_infix_op: $ => seq($._expr, $.general_infix_op, $._expr),

    // x'
    bound_postfix_op: $ => seq($._expr, $.general_postfix_op),

    // ((a + b) + c)
    parentheses: $ => seq('(', $._expr, ')'),

    // \A x \in Nat : P(x)
    bounded_quantification: $ => seq(
      choice($.forall, $.exists),
      commaList1($.quantifier_bound), ':', $._expr
    ),

    // \EE x : P(x)
    unbounded_quantification: $ => seq(
      choice($.forall, $.exists, $.temporal_forall, $.temporal_exists),
      commaList1($.identifier), ':', $._expr
    ),

    // CHOOSE r \in Real : r >= 0
    choose: $ => seq(
      'CHOOSE',
      choice($.identifier, $.tuple_of_identifiers),
      optional(seq($.set_in, $._expr)),
      ':',
      $._expr
    ),

    // {1, 2, 3, 4, 5}
    finite_set_literal: $ => seq('{', commaList($._expr), '}'),

    // { x \in S : P(x) }
    set_filter: $ => seq(
      '{',
      choice($.identifier, $.tuple_of_identifiers),
      $.set_in,
      $._expr,
      ':',
      $._expr,
      '}'
    ),

    // { f[x, y] : x, y \in S }
    set_map: $ => seq(
      '{', $._expr, ':', commaList1($.quantifier_bound), '}'
    ),

    // f[5]
    function_evaluation: $ => prec(16, seq(
      $._expr, '[', commaList1($._expr), ']'
    )),

    // [n \in Nat |-> 2*n]
    function_value: $ => seq(
      '[', commaList1($.quantifier_bound), $.all_map_to, $._expr, ']'
    ),

    // [Nat -> Nat]
    set_of_functions: $ => seq(
      '[', $._expr, $.maps_to, $._expr, ']'
    ),

    // [foo |-> 0, bar |-> 1]
    record_value: $ => seq(
      '[', commaList1(seq($.name, $.all_map_to, $._expr)), ']'
    ),

    // [foo : {0, 1}, bar : {0, 1}]
    set_of_records: $ => seq(
      '[', commaList1(seq($.name, ':', $._expr)), ']'
    ),

    // [f EXCEPT !.foo[bar].baz = 4, !.bar = 3]
    except: $ => seq(
      '[',
      $._expr,
      'EXCEPT',
      commaList1(
        seq(
          '!',
          repeat1(
            choice(
              seq('.', $.name),
              seq('[', commaList1($._expr), ']')
            )
          ),
          '=',
          $._expr
        )
      ),
      ']'
    ),

    // [f EXCEPT ![2] = @ + 1]
    prev_func_val: $ => '@',

    // <<1,2,3,4,5>>, <<>>
    tuple_literal: $ => seq(
      $.langle_bracket,
      commaList($._expr),
      $.rangle_bracket
    ),

    // [x ' > x]_<<x>>
    stepexpression_or_stutter: $ => seq(
      '[', $._expr, ']_', $._expr
    ),

    // <<x' > x>>_<<x>>
    stepexpression_no_stutter: $ => seq(
      $.langle_bracket,
      $._expr,
      $.rangle_bracket, token.immediate('_'),
      $._expr
    ),

    // WF_vars(ActionName)
    fairness: $ => seq(
      choice('WF_', 'SF_'), $._expr, '(', $._expr, ')'
    ),

    // IF a > b THEN a ELSE b
    if_then_else: $ => seq(
      'IF', $._expr, 'THEN', $._expr, 'ELSE', $._expr
    ),

    // CASE x = 1 -> "1" [] x = 2 -> "2" [] OTHER -> "3"
    case: $ => prec.left(seq(
      'CASE', $._expr, $.case_arrow, $._expr,
      repeat(seq($.case_box, $._expr, $.case_arrow, $._expr)),
      optional(seq($.case_box, 'OTHER', $.case_arrow, $._expr))
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
      $._expr
    ),

    // /\ x
    // /\ y
    conj: $ => repeat1(seq($.bullet_conj, $._expr)),

    // \/ x
    // \/ y
    disj: $ => repeat1(seq($.bullet_disj, $._expr)),
  }
});
