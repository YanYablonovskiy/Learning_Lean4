/-
In Lean 3, we can create simple functions from infix operators by using parentheses.

For example, (+1) is sugar for fun x, x + 1.

In Lean 4, we generalize this notation using · as a placeholder.

Here are a few examples:
-/

#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1 --applying function from the left, pairwise multiplication
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1) -- maps to the first element
-- [1, 3, 5]

/-
As in Lean 3, the notation is activated using parentheses, and the lambda abstraction is created by collecting the nested ·s.

The collection is interrupted by nested parentheses.

In the following example, two different lambda expressions are created.
-/
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
