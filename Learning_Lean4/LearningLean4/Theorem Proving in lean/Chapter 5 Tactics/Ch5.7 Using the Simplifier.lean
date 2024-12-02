/-
Whereas rewrite is designed as a surgical tool for manipulating a goal, the simplifier offers a more powerful
form of automation.

A number of identities in Lean's library have been tagged with the [simp] attribute,
and the simp tactic uses them to iteratively rewrite subterms in an expression.
-/
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp




example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

--using only simp by tagging
section

variable (x y z : Nat) (p₁ : Nat → Prop)
-- @[simp] axiom h:p₁ (x * y)
-- #check Nat.add_assoc

-- example: p₁ ((x + 0) * (0 + y * 1 + z * 0)) := by
--   simp

end

/-
In the first example, the left-hand side of the equality in the goal is simplified using
the usual identities involving 0 and 1, reducing the goal to x * y = x * y.

At that point, simp applies reflexivity to finish it off.

In the second example, simp reduces the goal to p (x * y), at which point
the assumption h finishes it off.

Here are some more examples with lists:
-/

section
open List

example (xs : List Nat) -- ++ is list concentation
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm] --not automatically used;
                      --otherwise left ys.length + xs.length = xs.length + ys.length
end

/-
As with rw, you can use the keyword at to simplify a hypothesis:
-/

example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

/-
Moreover, you can use a "wildcard" asterisk to simplify all the hypotheses and the goal:
-/
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * --h₁ becomes p(x+y); and h₂:p(x*z); goal becomes p (x + y) ∧ p (x * z)
  <;> constructor --applying And.intro, needing p (x + y) and p (x * z)
  <;> assumption  -- using h₁ h₂


/-
For operations that are commutative and associative, like multiplication on the natural numbers,
the simplifier uses these two facts to rewrite an expression, as well as left commutativity.

In the case of multiplication the latter is expressed
as follows: x * (y * z) = y * (x * z).

The local modifier tells the simplifier to use these
rules in the current file (or section or namespace, as the case may be).

It may seem that commutativity and left-commutativity are problematic,
in that repeated application of either causes looping.

But the simplifier detects identities that permute their arguments,
and uses a technique known as ordered rewriting.

This means that the system maintains an internal ordering of terms,
and only applies the identity if doing so decreases the order.

With the three identities mentioned above, this has the effect that
all the parentheses in an expression are associated to the right,
and the expressions are ordered in a canonical (though somewhat arbitrary) way.

Two expressions that are equivalent up to associativity and
commutativity are then rewritten to the same canonical form.
-/

example (w x y z : Nat)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption

--my version

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

/-
As with rewrite, you can send simp a list of facts to use, including general lemmas,
local hypotheses, definitions to unfold, and compound expressions.

The simp tactic also recognizes the ←t syntax that rewrite does.

In any case, the additional rules are added to the collection of identities
that are used to simplify a term.
-/
