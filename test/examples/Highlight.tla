A good mix of language constructs to illustrate highlighting.
Also includes various tests for scopes and reference highlighting.
---- MODULE Highlight ----
EXTENDS A, B, C
LOCAL INSTANCE D WITH X ← Y
CONSTANTS Foo, Const(_, _), □ _, _ ≺ _, _ ^*
VARIABLES bar, baz

const_ref ≜ Foo
const_op_ref ≜ Const(1, 2)

n ≜ -10 \* this is a single-line comment
s ≜ "Hello world!\nHere \"is a quote\""
p ≜ Nat
(* this (* is *) block comment *)
postfix ≜ var'
tuple ≜ (⟨1, 2, 3⟩)
action ≜ ⟨TRUE⟩_⟨bar, baz⟩
sq_action ≜ [TRUE]_⟨bar, baz⟩
jlist ≜
  ∧ 1
  ∧ ∨ 2
    ∨ 3 ∧ 4
    ∨ 5
  ∧ 6

func_literal ≜ [n ∈ Nat ↦ n]
f[n, m ∈ Nat, r ∈ Real] ≜ n
LOCAL g[⟨x, y, z⟩ ∈ S, ⟨u, v⟩ ∈ T] ≜ x
function_ref ≜ f
function_param_ref_test ≜ r

---- MODULE Inner ----
inner_def ≜ x
====
M2(a, b) ≜ INSTANCE Inner WITH x ← a, y ← b
module_ref ≜ M2!inner_def \* Need stack graphs to ref-highlight this
module_inner_ref ≜ inner_def

higher_order_op(a, param_op(_)) ≜ param_op(a)
op_parameter_scope_test ≜  param_op(1)

¬ x ≜ x
a ⊆ b ≜ a + b
x⁺ ≜ x
bound_symbol_ref(<> _, _ ‼ _, _ ^#) ≜
  ∧ {□TRUE, 1 ≺ 2, x^*}   \* constant
  ∧ {<>TRUE, a ‼ b, x^#}  \* parameter
  ∧ {¬TRUE, a ⊆ b, x⁺}    \* defined operator
nonfix_symbol_ref(<> _, _ ‼ _, _ ^#) ≜
  ∧ {□(TRUE), ≺(1, 2), ^*(x)}   \* constant
  ∧ {<>(TRUE), ‼(a, b), ^#(x)}  \* parameter
  ∧ {¬(TRUE), ⊆(a, b), ⁺(x)}    \* defined operator
standalone_symbol_ref(<> _, _ ‼ _, _ ^#) ≜
  ∧ op(□, ≺, ^*)  \* constant
  ∧ op(<>, ‼, ^#) \* parameter
  ∧ op(¬, ⊆, ⁺)   \* defined operator
symbol_scope_test ≜
  ∧ <>(1)
  ∧ a ‼ b
  ∧ x^#

RECURSIVE some_recursive_op(_), _ ⪯ _
some_recursive_op(x) ≜ some_recursive_op(x-1)

\* Scope testing for parameter highlighting in expressions
let_in_def ≜
  ∧ LET let_in_op(x) ≜ x IN let_in_op(1)
  ∧ let_in_op(1)
choose_def ≜
  ∧ CHOOSE ⟨x, y, z⟩ ∈ Nat : w < x < y < z
  ∧ w + x + y + z
apply(a, b, c, op(_, _, _)) ≜ op(a, b, c)
lambda_def ≜
  ∧ apply(1, 2, 3, LAMBDA x, y, z : w + x + y + z)
  ∧ w + x + y + z
unbounded_quant ≜
  ∧ ∃ x, y, z : w < x < y < z
  ∧ w + x + y + z
bounded_quant ≜
  ∧ ∃ x, y, z ∈ Nat : w < x < y < z
  ∧ w + x + y + z
bounded_quant_tuple ≜
  ∧ ∃ ⟨x, y, z⟩ ∈ Nat : w < x < y < z
  ∧ w + x + y + z
set_filter ≜
  ∧ {⟨ x, y, z ⟩ ∈ Nat : w < x < y < z}
  ∧ w + x + y + z
set_map ≜
  ∧ {w + x + y + z : x, y, z ∈ Nat}
  ∧ w + x + y + z
func_literal ≜
  ∧ [x, y, z ∈ Nat ↦ w + x + y + z]
  ∧ w + x + y + z

THEOREM TRUE
PROOF
<*>a. DEFINE s(n) ≜ n + 1
<*>b. 2
  <+>a. 3
  <*>b. QED
<*> QED
====

