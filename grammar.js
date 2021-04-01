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

    // Various syntactic elements and their unicode equivalents.
    def_eq: $ => choice('==', '≜'),
    set_in: $ => choice('\\in', '∈'),
    gets: $ => choice('<-', '⟵'),
    forall: $ => choice('\\A', '\\forall', '∀'),
    exists: $ => choice('\\E', '\\exists', '∃'),
    temporal_forall: $ => choice('\\AA'),
    temporal_exists: $ => choice('\\EE'),
    all_map_to: $ => choice('|->', '⟼', '↦'),
    maps_to: $ => choice('->', '⟶'),
    left_angle_bracket: $ => choice('<<', '〈'),
    right_angle_bracket: $ => choice('>>', '〉'),
    cross_product: $ => choice('\\X', '\\times', '×'),
    case_box: $ => choice('[]', '□'),
    case_arrow: $ => choice('->', '⟶'),
    bullet_conj: $ => choice('/\\', '∧'),
    bullet_disj: $ => choice('\\/', '∨'),

    // All prefix operators
    prefix_op: $ => choice(
      $.prefix_op_lnot,       $.prefix_op_union,    $.prefix_op_subset,
      $.prefix_op_domain,     $.prefix_op_negative, $.prefix_op_enabled,
      $.prefix_op_unchanged,  $.prefix_op_always,   $.prefix_op_eventually
    ),

    // Prefix operators are given highest value in precedence range.
    prefix_op_lnot:       $ => $.prec(4, choice('\\lnot', '\\neg', '~', '¬')),
    prefix_op_union:      $ => $.prec(8, 'UNION'),
    prefix_op_subset:     $ => $.prec(8, 'SUBSET'),
    prefix_op_domain:     $ => $.prec(9, 'DOMAIN'),
    prefix_op_negative:   $ => $.prec(12, '-'),
    prefix_op_enabled:    $ => $.prec(15, 'ENABLED'),
    prefix_op_unchanged:  $ => $.prec(15, 'UNCHANGED'),
    prefix_op_always:     $ => $.prec(15, choice('[]', '□')),
    prefix_op_eventually: $ => $.prec(15, choice('<>', '⋄')),

    // Infix operators
    old_infix_op: $ => choice(
      '!!',   '#',    '##',   '$',    '$$',   '%',    '%%',
      '&',    '&&',   '(+)',  '(-)',  '(.)',  '(/)',  '(\\X)',
      '*',    '**',   '+',    '++',   '-',    '-+->', '--',
      '-|',   '..',   '...',  '/',    '//',   '/=',   '/\\',
      '::=',  ':=',   ':>',   '<',    '<:',   '<=>',  '=',
      '=<',   '=>',   '=|',   '>',    '>=',   '?',    '??',
      '@@',   '\\',   '\\/',  '^',    '^^',   '|',    '|-',
      '|=',   '||',   '~>',   '.',    '<=',
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
      '\\equiv',    '\\oplus',      '\\sqsupset',   '\\notin',
    ),

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

    infix_op_implies:     $ => prec(1, choice('=>', '⟹')),
    infix_op_plus_arrow:  $ => prec(2, choice('-+->', '⇸', '⍆', '⥅')),
    infix_op_equiv:       $ => prec(2, choice('\\equiv', '≡')),
    infix_op_iff:         $ => prec(2, choice('<=>', '⟺')),
    infix_op_leads_to:    $ => prec(2, choice('~>', '⇝')),
    infix_op_land:        $ => prec.left(3, choice('/\\', '\\land', '∧')),
    infix_op_lor:         $ => prec.left(3, choice('\\/', '\\lor', '∨')),
    infix_op_assign:      $ => prec(5, ':='),
    infix_op_bnf_rule:    $ => prec(5, '::='),
    infix_op_eq:          $ => prec(5, '='),
    infix_op_neq:         $ => prec(5, choice('/=', '#', '≠')),
    infix_op_lt:          $ => prec(5, '<'),
    infix_op_gt:          $ => prec(5, '>'),
    infix_op_leq:         $ => prec(5, choice('<=', '\\leq', '≤')),
    infix_op_geq:         $ => prec(5, choice('>=', '\\geq', '≥')),
    infix_op_approx:      $ => prec(5, choice('\\approx', '≈')),
    infix_op_rs_ttile:    $ => prec(5, choice('|-', '⊢')),
    infix_op_rd_ttile:    $ => prec(5, choice('|=', '⊨')),
    infix_op_ls_ttile:    $ => prec(5, choice('-|', '⊣')),
    infix_op_ld_ttile:    $ => prec(5, choice('=|', '⫤')),
    infix_op_asymp:       $ => prec(5, choice('\\asymp', '≍')),
    infix_op_cong:        $ => prec(5, choice('\\cong', '≅')),
    infix_op_doteq:       $ => prec(5, choice('\\doteq', '≐')),
    infix_op_gg:          $ => prec(5, choice('\\gg', '≫')),
    infix_op_ll:          $ => prec(5, choice('\\ll', '≪')),
    infix_op_in:          $ => prec(5, choice('\\in', '∈')),
    infix_op_notin:       $ => prec(5, choice('\\notin', '∉')),
    infix_op_prec:        $ => prec(5, choice('\\prec', '≺')),
    infix_op_succ:        $ => prec(5, choice('\\succ', '≻')),
    infix_op_preceq:      $ => prec(5, choice('\\preceq', '⪯')),
    infix_op_succeq:      $ => prec(5, choice('\\succeq', '⪰')),
    infix_op_propto:      $ => prec(5, choice('\\propto', '∝')),
    infix_op_sim:         $ => prec(5, choice('\\sim', '∼')),
    infix_op_simeq:       $ => prec(5, choice('\\simeq', '≃')),
    infix_op_sqsubset:    $ => prec(5, choice('\\sqsubset', '⊏')),
    infix_op_sqsupset:    $ => prec(5, choice('\\sqsupset', '⊐')),
    infix_op_sqsubseteq:  $ => prec(5, choice('\\sqsubseteq', '⊑')),
    infix_op_sqsupseteq:  $ => prec(5, choice('\\sqsupseteq', '⊒')),
    infix_op_subset:      $ => prec(5, choice('\\subset', '⊂')),
    infix_op_supset:      $ => prec(5, choice('\\supset', '⊃')),
    infix_op_subseteq:    $ => prec(5, choice('\\subseteq', '⊆')),
    infix_op_supseteq:    $ => prec(5, choice('\\supseteq', '⊇')),
    infix_op_compose:     $ => prec.left(6, '@@'),
    infix_op_map_to:      $ => prec(7, ':>'),
    infix_op_map_from:    $ => prec(7, '<:'),
    infix_op_setminus:    $ => prec(8, '\\'),
    infix_op_cap:         $ => prec.left(8, choice('\\cap', '∩')),
    infix_op_cup:         $ => prec.left(8, choice('\\cup', '∪')),
    infix_op_2dots:       $ => prec(9, '..'),
    infix_op_3dots:       $ => prec(9, choice('...', '…')),
    infix_op_plus:        $ => prec.left(10, '+'),
    infix_op_plusplus:    $ => prec.left(10, '++'),
    infix_op_oplus:       $ => prec.left(10, choice('\\oplus', '⊕')),
    infix_op_ominus:      $ => prec.left(11, choice('\\ominus', '⊖')),
    infix_op_mod:         $ => prec(11, '%'),
    infix_op_modmod:      $ => prec.left(11, '%%'),
    infix_op_vert:        $ => prec.left(11, '|'),
    infix_op_vertvert:    $ => prec.left(11, choice('||', '‖')),
    infix_op_minus:       $ => prec.left(11, '-'),
    infix_op_minusminus:  $ => prec.left(11, '--'),
    infix_op_amp:         $ => prec.left(13, '&'),
    infix_op_ampamp:      $ => prec.left(13, '&&'),
    infix_op_odot:        $ => prec.left(13, choice('\\odot', '⊙')),
    infix_op_oslash:      $ => prec(13, choice('\\oslash', '⊘')),
    infix_op_otimes:      $ => prec.left(13, choice('\\otimes', '⊗')),
    infix_op_mul:         $ => prec.left(13, '*'),
    infix_op_mulmul:      $ => prec.left(13, '**'),
    infix_op_slash:       $ => prec(13, '/'),
    infix_op_slashslash:  $ => prec(13, '//'),
    infix_op_bigcirc:     $ => prec.left(13, choice('\\bigcirc', '◯')),
    infix_op_bullet:      $ => prec.left(13, choice('\\bullet', '●')),
    infix_op_div:         $ => prec(13, choice('\\div', '÷')),
    infix_op_circ:        $ => prec.left(13, choice('\\circ', '∘')),
    infix_op_star:        $ => prec.left(13, choice('\\star', '⋆')),
    infix_op_excl:        $ => prec(13, choice('!!', '‼')),
    infix_op_hashhash:    $ => prec.left(13, '##'),
    infix_op_dol:         $ => prec.left(13, '$'),
    infix_op_doldol:      $ => prec.left(13, '$$'),
    infix_op_qq:          $ => prec.left(13, '??'),
    infix_op_sqcap:       $ => prec.left(13, choice('\\sqcap', '⊓')),
    infix_op_sqcup:       $ => prec.left(13, choice('\\sqcup', '⊔')),
    infix_op_uplus:       $ => prec.left(13, choice('\\uplus', '⊎')),
    infix_op_wr:          $ => prec(14, choice('\\wr', '≀')),
    infix_op_cdot:        $ => prec.left(14, choice('\\cdot', '⋅')),
    infix_op_pow:         $ => prec(14, '^'),
    infix_op_powpow:      $ => prec(14, '^^'),
    infix_op_rfield:      $ => prec.left(17, '.'),

    // Postfix operators
    postfix_op: $ => choice(
      $.postfix_op_plus,    $.postfix_op_ast,
      $.postfix_op_hash,    $.postfix_op_prime
    ),

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
        $.recurisive_operator_declaration,
        //$.use_or_hide
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
    recurisive_operator_declaration: $ => seq(
      'RECURSIVE', commaList1($.operator_declaration)
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
      $.def_eq,
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
      $.def_eq,
      $.expression
    ),

    // x, y, z \in S
    quantifier_bound: $ => seq(
      choice(
        $.tuple_of_identifiers,
        commaList1($.identifier)
      ),
      $.set_in,
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
      $.gets,
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
      $.def_eq,
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
      $.boolean
    ),

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
      choice($.forall, $.exists),
      commaList1($.quantifier_bound), ':', $.expression
    ),

    // \EE x : P(x)
    unbounded_quantification: $ => seq(
      choice($.forall, $.exists, $.temporal_forall, $.temporal_exists),
      commaList1($.identifier), ':', $.expression
    ),

    // CHOOSE r \in Real : r >= 0
    choose: $ => seq(
      'CHOOSE',
      choice($.identifier, $.tuple_of_identifiers),
      optional(seq($.set_in, $.expression)),
      ':',
      $.expression
    ),

    // {1, 2, 3, 4, 5}
    finite_set_literal: $ => seq('{', commaList($.expression), '}'),

    // { x \in S : P(x) }
    set_filter: $ => seq(
      '{',
      choice($.identifier, $.tuple_of_identifiers),
      $.set_in,
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
      '[', commaList1($.quantifier_bound), $.all_map_to, $.expression, ']'
    ),

    // [Nat -> Nat]
    set_of_functions: $ => seq(
      '[', $.expression, $.maps_to, $.expression, ']'
    ),

    // [foo |-> 0, bar |-> 1]
    record_definition: $ => seq(
      '[', commaList1(seq($.name, $.all_map_to, $.expression)), ']'
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
    tuple_literal: $ => seq(
      $.left_angle_bracket,
      commaList($.expression),
      $.right_angle_bracket
    ),

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
      $.left_angle_bracket,
      $.expression,
      $.right_angle_bracket, token.immediate('_'),
      $.expression
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
      'CASE', $.expression, $.case_arrow, $.expression,
      repeat(seq($.case_box, $.expression, $.case_arrow, $.expression)),
      optional(seq($.case_box, 'OTHER', $.case_arrow, $.expression))
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

    // /\ x
    // /\ y
    conj: $ => repeat1(seq($.bullet_conj, $.expression)),

    // \/ x
    // \/ y
    disj: $ => repeat1(seq($.bullet_disj, $.expression)),

    // TRUE, FALSE, BOOLEAN
    boolean: $ => choice('TRUE', 'FALSE', 'BOOLEAN'),
  }
});
