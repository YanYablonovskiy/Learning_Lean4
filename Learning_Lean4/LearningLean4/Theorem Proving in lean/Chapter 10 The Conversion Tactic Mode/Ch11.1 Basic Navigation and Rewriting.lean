/-
The Conversion Tactic Mode

Inside a tactic block, one can use the keyword conv to enter
conversion mode. This mode allows to travel inside assumptions
and goals, even inside function abstractions and dependent arrows,
to apply rewriting or simplifying steps.

Basic navigation and rewriting:

As a first example, let us prove example
(a b c : Nat) : a * (b * c) = a * (c * b)
(examples in this file are somewhat artificial since other
tactics could finish them immediately).

The naive first attempt is to enter tactic mode and
try rw [Nat.mul_comm].

But this transforms the goal into b * c * a = a * (c * b),
after commuting the very first multiplication appearing in the term.

There are several ways to fix this issue, and one way is to use a
more precise tool: the conversion mode.

The following code block shows the current target after each line.
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    congr
    -- 2 goals: ⊢ a, ⊢ b * c
    rfl
    -- ⊢ b * c
    rw [Nat.mul_comm]

/-
The above snippet shows three navigation commands:

lhs navigates to the left-hand side of a relation (equality, in this case).

There is also a rhs to navigate to the right-hand side.

congr creates as many targets as there are (nondependent and explicit) arguments
to the current head function (here the head function is multiplication).

rfl closes target using reflexivity.

Once arrived at the relevant target, we can use rw as in normal tactic mode.

The second main reason to use conversion mode is to
rewrite under binders.

Suppose we want to prove example
(fun x : Nat => 0 + x) = (fun x => x).

The naive first attempt is to enter tactic mode and try rw [Nat.zero_add].

But this fails with a frustrating


error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x

The solution is:
-/

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]

/-
where intro x is the navigation command entering inside the fun binder.

Note that this example is somewhat artificial, one could also do:
-/
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]

/-
or just
-/

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp

/-
conv can also rewrite a hypothesis h from the local context,
using conv at h.
-/
