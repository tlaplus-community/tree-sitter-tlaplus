A good mix of language constructs to illustrate highlighting.
---- MODULE Highlight ----
CONSTANTS Foo, Const(_, _), _ ≺ _
VARIABLE Bar

const_ref ≜ Foo
const_op_ref ≜ Const(1, 2)
const_infix_op_ref ≜ 1 ≺ 2


n == -10
s == "hello, world!"
p == Nat \* asdf
(* this (* is *) block comment *)
postfix == var'
tuple == (<<1,2,3>>)
set == {n \in Nat : n % 2 = 0}
action == <<TRUE>>_Bar
sq_action == [TRUE]_Bar
jlist ==
    /\ 1
    /\ \/ 2 ∧ 10
       \/ 3
    /\ 4

func == [n \in Nat |-> n]
f[n, m \in Nat, r \in Real] == n
g[<<x, y, z>> \in S, <<u, v>> \in T] == x
function_ref ≜ f

apply(a, b, op(_, _)) == op(a, b)
result == apply(1, 2, LAMBDA x, y : x + y)

M2(a, b, -. _) == INSTANCE M1 WITH \neg <- -., A <- B
module_ref == M2

higher_order_op(a, _‖_, g(_)) ≜ g(a ‖ Bar)
op_ref ≜ higher_order_op(1, +, -.)
op_parameter_scope_test ≜ a ‖ b

a * b ≜ a + b
infix_op_ref ≜ 1 * 2

let_in_def ≜ LET let_in_op(x) ≜ x IN let_in_op(1)
let_in_op_ref_test ≜ let_in_op(1)

THEOREM TRUE
PROOF
<*>a. DEFINE s(n) ≜ n + 1
<*>b. 2
  <+>a. 3
  <*>b. QED
<*> QED
====
