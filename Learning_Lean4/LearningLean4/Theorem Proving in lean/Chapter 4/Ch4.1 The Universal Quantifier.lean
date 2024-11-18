/-
The last chapter introduced you to methods that construct proofs of statements involving the propositional connectives.
In this chapter, we extend the repertoire of logical constructions to include the universal and existential quantifiers,
and the equality relation.

-/
set_option linter.unusedVariables false
/-
Notice that if α is any type, we can represent a unary predicate p on α as an object of type α → Prop.
In that case, given x : α, p x denotes the assertion that p holds of x.
Similarly, an object r : α → α → Prop denotes a binary relation on α:
           given x y : α, r x y denotes the assertion that x is related to y.

-/

variable (α₁ α₂: Type _)
#check α₁ → Prop
#check α₁ → α₁ → Prop

/-
The universal quantifier, ∀ x : α, p x is supposed to denote the assertion that "for every x : α, p x" holds.
-/
#check ∀ x: α₁, α₂ -- α₁ → α₂ : Type (max ?u.32 ?u.35)
#check (x: α₁) → α₂ --α₁ → α₂ : Type (max ?u.43 ?u.46)
-- really the same thing, and if α₂ is Prop we get the forall quantifier.

/-
As with the propositional connectives, in systems of natural deduction, "forall" is governed by an introduction and elimination rule.
Informally, the introduction rule states:
-/

/- Given a proof of p x, in a context where x : α is arbitrary, we obtain a proof ∀ x : α, p x. -/

-- p x is in Prop type universe

/-
The elimination rule states:

Given a proof ∀ x : α, p x and any term t : α, we obtain a proof of p t.
-/
variable (p q: Prop)
#check α₁ → Prop
#check Type → Prop
#check Prop → α₁
#check Prop → Prop -- type universes
#check p → q
#check α₁ → p
#check α₂ → p --both are Prop
#check α₂ → α₁ --not same type everytime
/-
As was the case for implication, the propositions-as-types interpretation now comes into play.
Remember the introduction and elimination rules for dependent arrow types:
-/

/-
Given a term t of type β x, in a context where x : α is arbitrary,
we have (fun x : α => t) : (x : α) → β x.
-/
variable (α: Type) {βx: Type _}

example {x: α} (t: βx) : (α → βx) := fun x => t --Given a term t of type β x, in a context where x : α is arbitrary, we have (fun x : α => t) : (x : α) → β x.

#check {x: α} → βx --{x : α} → βx : Type ?u.232
#check α → βx
--this is the dependent arrow intro, and if we change it to Prop:
variable {pβx: Prop}
#check {x:α} → pβx -- ∀ {x : α}, pβx : Prop
#check α → pβx
/-
The elimination rule states: -- for dependent arrows.
-/

/-
Given a term s : (x : α) → β x and any term t : α, we have s t : β t.
-/
variable (h: (x : α) → βx)

example (t:α): βx := (@h t)

/-
In the case where pβx has type Prop, if we replace (x : α) → β x
with ∀ x : α, p x, we can read these as the correct rules for building proofs
involving the universal quantifier.
-/
--Prop version
variable (hp: {x : α} → pβx)

example (t:α): pβx := @hp t
-- we dont lose data unlike existential, because a member can be produced trivially
-- via any t:α( we can make an arbitrary choice)

/-
The Calculus of Constructions therefore identifies dependent arrow types with forall-expressions in this way.

If p is any expression, ∀ x : α, p is nothing more than alternative notation for (x : α) → p,
with the idea that the former is more natural than the latter in cases where p is a proposition.
Typically, the expression p will depend on x : α.

Recall that, in the case of ordinary function spaces, we could interpret α → β as the special case of
(x : α) → β in which β does not depend on x.

Similarly, we can think of an implication p → q between propositions as the special case of
∀ x : p, q in which the expression q does not depend on x.

--due to proof irrelevance, this is always the case; if one term of p proves q then any does.

Here is an example of how the propositions-as-types correspondence gets put into practice.
-/

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  --∀ (α : Type) (p q : α → Prop), (∀ (x : α), p x ∧ q x) → ∀ (y : α), p y
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

/-
As a notational convention, we give the universal quantifier the widest scope possible,
so parentheses are needed to limit the quantifier over x to the hypothesis in the example above.

The canonical way to prove ∀ y : α, p y is to take an arbitrary y, and prove p y.

This is the introduction rule.

Now, given that h has type ∀ x : α, p x ∧ q x,
the expression h y has type p y ∧ q y.

This is the elimination rule.

Taking the left conjunct gives the desired conclusion, p y.
R
emember that expressions which differ up to renaming of bound variables are considered to be equivalent.

So, for example, we could have used the same variable, x, in both the hypothesis and conclusion,
and instantiated it by a different variable, z, in the proof:
-/
example (α : Type)(p q : α → Prop): (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)

/-
As another example, here is how we can express the assumption that a relation, r, is transitive:
-/
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z : α, r x y → r y z → r x z) --terms of Prop; meaning implication of truth

#check @trans_r

--∀ x y z: α, (x ~ y) implies if (y ~ z) then (x ~ z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c) --a ~ b, b ~ c

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z


#check trans_r a b c -- r a b → r b c → r a c
-- if we have trans for r, and terms a b c in α. then we get the statement of transitivity for a b c

#check trans_r a b c hab -- r b c → r a c

-- applying to r a b → r b c → r a c, a term of the first type
-- to arrive at r b c → r a c


#check trans_r a b c hab hbc -- r a c

/-
Think about what is going on here.

When we instantiate trans_r at the values a b c, we end up with a proof of r a b → r b c → r a c.

Applying this to the "hypothesis" hab : r a b, we get a proof of the implication r b c → r a c.

Finally, applying it to the hypothesis hbc yields a proof of the conclusion r a c.
-/

/-
In situations like this, it can be tedious to supply the arguments a b c, when they can be inferred from hab hbc.
For that reason, it is common to make these arguments implicit:
-/
variable (trans_r_imp : ∀ {x y z : α}, r x y → r y z → r x z)

#check trans_r_imp hab
#check trans_r_imp hab hbc

/-
The advantage is that we can simply write trans_r hab hbc as a proof of r a c.

A disadvantage is that Lean does not have enough information to infer the types
of the arguments in the expressions trans_r and trans_r hab.

The output of the first #check command is r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3,
indicating that the implicit arguments are unspecified in this case.

Here is an example of how we can carry out elementary reasoning with an equivalence relation:

-/

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

/-
To get used to using universal quantifiers,
you should try some of the exercises at the end of this section.
-/

/-
It is the typing rule for dependent arrow types, and the universal quantifier in particular,
that distinguishes Prop from other types.

Suppose we have α : Sort i and β : Sort j, where the expression β may depend on a variable x : α.

-- a type from universe Sort i and a type from universe Sort j

Then (x : α) → β is an element of Sort (imax i j), where imax i j is the maximum of i and j if j is not 0,
and 0 otherwise.

--(x : α) → β  a type from universe Sort (imax i j)

-/
#check ∀ x: α₁, α₂ -- α₁ → α₂ : Type (max ?u.32 ?u.35)
#check (x: α₁) → α₂ --α₁ → α₂ : Type (max ?u.43 ?u.46)


/-
The idea is as follows. If j is not 0, then (x : α) → β is an element of Sort (max i j).

In other words, the type of dependent functions from α to β "lives" in the universe whose index is the maximum of i and j.

Suppose, however, that β is of Sort 0, that is, an element of Prop.

In that case, (x : α) → β is an element of Sort 0 as well, no matter which type universe α lives in.

In other words, if β is a proposition depending on α, then ∀ x : α, β is again a proposition.

This reflects the interpretation of Prop as the type of propositions rather than data,
and it is what makes Prop impredicative.
-/



/-
The term "predicative" stems from foundational developments around the turn of the twentieth century,
when logicians such as Poincaré and Russell blamed set-theoretic paradoxes on the "vicious circles"
that arise when we define a property by quantifying over a collection that includes the very property
being defined.

Notice that if α is any type, we can form the type α → Prop of all predicates on α (the "power type of α").

The impredicativity of Prop means that we can form propositions that quantify over α → Prop.

In particular, we can define predicates on α by quantifying over all predicates on α,
which is exactly the type of circularity that was once considered problematic.
-/
variable (q : α → Prop) (x:α)
#check ∀ (p: α → Prop), ¬p x --∀ (p : α → Prop), ¬p x : Prop

-- ' no statement is true of x '
