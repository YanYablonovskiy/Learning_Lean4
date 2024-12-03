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

def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]

--my versions

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h]
  --makes goal f m 1 = 1
  simp [←h']
  -- makes goal f 0 1 = 1
  --exact Eq.refl (f 0 1)
  simp [f] --uses f 0 1 to get 1

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h]
  --makes goal f m 1 = 1
  simp [←h']
  -- makes goal f 0 1 = 1
  exact Eq.refl (f 0 1)

/-
A common idiom is to simplify a goal using local hypotheses:
-/

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂] --doesnt work with just h₁, uses both facts h₁ h₂ to apply to hypothesis

--my versions
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₂]
  simp [h₁]

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₂, h₁] --simp is commutative

--tactic-less
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := 
  have h:f k = f 0 := congrArg f h₂
  show f k = 0 from Eq.trans h h₁


/-
To use all the hypotheses present in the local context when simplifying, 
we can use the wildcard symbol, *:
-/
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*] -- same as simp [h₁, h₂]


/-
Here is another example:
-/

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

--here * takes the local hypotheses; making u + x = z + y + u -> u + y +z = z + y + u
-- add_assoc can do many things, here the branch that works puts u + (y + z) = z + y + u
-- add_left_comm makes (y + z) + u = z + y + u ( note (y + z) + u is just y + z + u) )
-- then add_left_comm again makes z + y + u = z + y + u and finishes via refl


--since the Nats are in our simp, * works
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*]

/-
The simplifier will also do propositional rewriting. 

For example, using the hypothesis p, it rewrites p ∧ q to q and p ∨ q to true, 
which it then proves trivially. 

Iterating such rewrites produces nontrivial propositional reasoning.
-/
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]


--my versions
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [hp] --just need hp; which rewrites goal of p ∧ q  ↔ q to q ↔ q


example (p q : Prop) (hp : p) : p ∨ q := by
  simp [hp] --just need hp, which uses or intro to re-write

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [hp] --uses And.intro on hp to get goal q ∨ r
  simp [hq] --uses Or.inl hq

/-
The next example simplifies all the hypotheses, and then uses them to prove the goal.
-/

example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

/-
One thing that makes the simplifier especially useful is that its capabilities can grow as a library develops. 

For example, suppose we define a list operation that symmetrizes its input by appending its reversal:
-/
def mk_symm (xs : List α) :=
  xs ++ xs.reverse

/-
Then for any list xs, reverse (mk_symm xs) is equal to mk_symm xs, 
which can easily be proved by unfolding the definition:
-/
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

/-
We can now use this theorem to prove new results:
-/
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption

--my one
example (xs ys : List Nat)
        : (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
simp

/-
But using reverse_mk_symm is generally the right thing to do, 
and it would be nice if users did not have to invoke it explicitly. 

You can achieve that by marking it as a simplification rule when the theorem is defined:
-/
section 
@[simp] theorem reverse_mk_symm_simp (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end

/-
The notation @[simp] declares reverse_mk_symm to have the [simp] attribute, 
and can be spelled out more explicitly:
-/

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

/-
The attribute can also be applied any time after the theorem is declared:
-/

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption


/-
Once the attribute is applied, however, there is no way to permanently remove it; 
it persists in any file that imports the one where the attribute is assigned. 

As we will discuss further in Attributes, one can limit the scope of an 
attribute to the current file or section using the local modifier:
-/
section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end

/-
Outside the section, the simplifier will no longer use reverse_mk_symm by default.

Note that the various simp options we have discussed --- giving an explicit list of rules, 
and using at to specify the location --- can be combined, but the order they are listed is rigid. 

You can see the correct order in an editor by placing the cursor on the simp identifier 
to see the documentation string that is associated with it.

There are two additional modifiers that are useful. 

By default, simp includes all theorems that have been marked with the attribute [simp].

Writing simp only excludes these defaults, allowing you to use a 
more explicitly crafted list of rules. 

In the examples below, the minus sign and only are used 
to block the application of reverse_mk_symm.
-/
example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm_simp,-reverse_mk_symm] at h; assumption 

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption

/-
The simp tactic has many configuration options. 

For example, we can enable contextual simplifications as follows:
-/
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })

/-
With contextual := true, the simp tactic uses the fact that x = 0 when simplifying y + x = y, 
and x ≠ 0 when simplifying the other branch. 

Here is another example:
-/

example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp (config := { contextual := true })

/-
Another useful configuration option is arith := true which enables arithmetical simplifications. 

It is so useful that simp_arith is a shorthand for simp (config := { arith := true }):
-/
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp_arith
