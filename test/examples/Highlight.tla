A good mix of language constructs to illustrate highlighting.
Also includes various tests for scopes and reference highlighting.
---- MODULE Highlight ----
EXTENDS A, B, C
LOCAL INSTANCE D WITH X ← Y
CONSTANTS Foo, Const(_, _), _ ≺ _
VARIABLES bar, baz

const_ref ≜ Foo
const_op_ref ≜ Const(1, 2)
const_infix_op_ref ≜ 1 ≺ 2

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

apply(a, b, op(_, _)) ≜ op(a, b)
result ≜ apply(1, 2, LAMBDA x, y : x + y + z)

M2(a, b, -. _) ≜ INSTANCE M1 WITH ¬ ← -., x ← a, y ← b
module_ref ≜ M2!some_m2_op

higher_order_op(a, _‖_, g(_)) ≜ g(a ‖ bar)
op_ref ≜ higher_order_op(1, +, -.)
op_parameter_scope_test ≜ a ‖ b

a * b ≜ a + b
infix_op_ref ≜ 1 * 2

let_in_def ≜
  ∧ LET let_in_op(x) ≜ x IN let_in_op(1)
  ∧ let_in_op(1)

RECURSIVE some_recursive_op(_), _ ⪯ _

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
  ∧ {x + y + z : x, y, z ∈ Nat}
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

