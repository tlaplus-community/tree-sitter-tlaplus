A good mix of language constructs to illustrate highlighting.
---- MODULE Highlight ----
CONSTANTS Foo, Const(_, _)
VARIABLE Bar
n == -10
s == "hello, world!"
p == Nat \* asdf
(* this (* is *) block comment *)
postfix == var'
tuple == (<<1,2,3>>)
set == {n \in Nat : n % 2 = 0}
action == <<TRUE>>_Foo
sq_action == [TRUE]_Foo
func == [n \in Nat |-> n]
jlist ==
    /\ 1
    /\ \/ 2
       \/ 3
    /\ 4
f[n, m \in Nat, r \in Real] == n
g[<<x, y, z>> \in S, <<u, v>> \in T] == x
apply(a, b, op(_, _)) == op(a, b)
apply(a, b, _ + _) == a > b
a + b == a
result == apply(1, 2, LAMBDA x, y : x + y)
M2(a, b, -. _) == INSTANCE M1 WITH \neg <- -., A <- B
apply == M2

ref == Foo + Const(a, b)

a ≺ b ≜ a < b
op2(a, _‖_, g(_)) ≜ Const(f(g(a ‖ Bar)), b)

a + b ≜ a ‖ b

THEOREM TRUE
PROOF
<*>a. 1
<*>b. 2
  <+>a. 3
  <*>b. QED
<*> QED
====
