/-
We have seen that the version of the Calculus of Constructions that has
been implemented in Lean includes dependent function types, inductive types,
and a hierarchy of universes that starts with an impredicative,
proof-irrelevant Prop at the bottom.

In this chapter, we consider ways of extending the CIC with
additional axioms and rules.

Extending a foundational system in such a way is often convenient;
it can make it possible to prove more theorems, as well as make
it easier to prove theorems that could have been proved otherwise.

But there can be negative consequences of adding additional axioms,
consequences which may go beyond concerns about their correctness.

In particular, the use of axioms bears on the computational content
of definitions and theorems, in ways we will explore here.
-/

-- Let's start by defining a simple axiom and see its implications.

-- Axiom: There exists an element of type `α` for any type `α`.
axiom choice (α : Type) : α

-- Using the axiom to define a function that returns an element
-- of any type.
noncomputable def getElement (α : Type) : α := choice α

-- Example usage of the function.
noncomputable def exampleNat : Nat := getElement Nat

-- Note: The above axiom is not constructive and does not provide a
-- specific element.

-- It only asserts the existence of such an element,
-- which affects the computational content.

/-

Lean is designed to support both computational and classical reasoning.

Users that are so inclined can stick to a "computationally pure" fragment,
which guarantees that closed expressions in the system evaluate to canonical
normal forms.

In particular, any closed computationally pure expression of type Nat,
for example, will reduce to a numeral.

-/

/-
Lean's standard library defines an additional axiom, propositional extensionality,
and a quotient construction which in turn implies the principle of function extensionality.

These extensions are used, for example, to develop theories of sets and finite sets.

We will see below that using these theorems can block evaluation in Lean's kernel,
so that closed terms of type Nat no longer evaluate to numerals.

But Lean erases types and propositional information when compiling definitions
to bytecode for its virtual machine evaluator, and since these axioms only add
new propositions, they are compatible with that computational interpretation.

Even computationally inclined users may wish to use the
classical law of the excluded middle to reason about computation.

This also blocks evaluation in the kernel, but it is compatible with compilation to bytecode.
-/
universe u

axiom propExt : ∀ {α : Sort u} {p q : α → Prop}, (∀ x, p x ↔ q x) → p = q

--iff means equivalent propositions

noncomputable def examplePropExt (α : Sort u) (p q : α → Prop) (h : ∀ x, p x ↔ q x) : p = q :=
  propExt h
-- dont need this as an axiom, can be proven with quotient and propext
axiom funExt : ∀ {α β : Sort u} {f g : α → β}, (∀ x, f x = g x) → f = g

noncomputable def exampleFunExt (α β : Sort u) (f g : α → β) (h : ∀ x, f x = g x) : f = g :=
  funExt h

axiom excludedMiddle : ∀ (p : Prop), p ∨ ¬p

noncomputable def exampleExcludedMiddle (p : Prop) : p ∨ ¬p :=
  excludedMiddle p

/-
The standard library also defines a choice principle that is entirely antithetical to a computational interpretation,
since it magically produces "data" from a proposition asserting its existence.

Its use is essential to some classical constructions, and users can import it when needed.

But expressions that use this construction to produce data do not have computational content,
and in Lean we are required to mark such definitions as noncomputable to flag that fact.
-/

/-
Using a clever trick (known as Diaconescu's theorem), one can use propositional extensionality, function extensionality,
and choice to derive the law of the excluded middle.

As noted above, however, use of the law of the excluded middle is still compatible with bytecode compilation and code extraction,
as are other classical principles, as long as they are not used to manufacture data.

To summarize, then, on top of the underlying framework of universes, dependent function types, and inductive types,
the standard library adds three additional components:
-/


axiom classicalChoice : ∀ {α : Type u} (p : α → Prop), (∃ x, p x) → {x // p x}

noncomputable def exampleClassicalChoice {α : Type u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  classicalChoice p h

/-
To summarize, then, on top of the underlying framework of universes, dependent function types, and inductive types,
the standard library adds three additional components:

⬝ the axiom of propositional extensionality
⬝ a quotient construction, which implies function extensionality
⬝ a choice principle, which produces data from an existential proposition.

--can be used to derive excluded middle


The first two of these block normalization within Lean, but are compatible with bytecode evaluation,
whereas the third is not amenable to computational interpretation.

We will spell out the details more precisely below.
-/
