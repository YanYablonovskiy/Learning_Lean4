/-
This is a good place to introduce another device Lean offers to help structure long proofs, namely,
the have construct, which introduces an auxiliary subgoal in a proof.

Here is a small example, adapted from the last section:

-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left --proof of hp by h
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

/-
Internally, the expression
have h : p := s; t
produces the term
(fun (h : p) => t) s.
--s is term of type p hence proof of p, and t is a proof using p
In other words, s is a proof of p, t is a proof of the desired conclusion assuming h : p,
and the two are combined by a lambda abstraction and application.

This simple device is extremely useful when it comes to structuring long proofs,
 since we can use intermediate have's as stepping stones leading to the final goal.
-/


/-
Lean also supports a structured way of reasoning backwards from a goal,
which models the "suffices to show" construction in ordinary mathematics.

The next example simply permutes the last two lines in the previous proof.
-/

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h


/-
Writing suffices hq : q leaves us with two goals.

First, we have to show that it indeed suffices to show q,
by proving the original goal of q ∧ p with the additional hypothesis hq : q.

Finally, we have to show q.
-/
