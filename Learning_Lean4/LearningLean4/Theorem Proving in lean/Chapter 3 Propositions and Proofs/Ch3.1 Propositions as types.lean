/-
One strategy for proving assertions about objects defined in the language of dependent type theory is
to layer an assertion language and a proof language on top of the definition language.

But there is no reason to multiply languages in this way:
dependent type theory is flexible and expressive, and there is no reason we cannot represent assertions
and proofs in the same general framework.

For example, we could introduce a new type, Prop, to represent propositions,
and introduce constructors to build new propositions from others.
-/

def Implies (α : Prop) (β: Prop): Prop := α → β


#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

/-
We could then introduce, for each element p : Prop, another type Proof p, for the type of proofs of p.
An "axiom" would be a constant of such a type.
-/

def Proof (α : Prop): Type := Sort 0  -- This isnt actually the way Proof works, it will likely be a new type
                                     -- based on a.

#check Proof   -- Proof : Prop → Type

axiom and_comm_1 (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm_1 p q     -- Proof (Implies (And p q) (And q p))


/-
In addition to axioms, however, we would also need rules to build new proofs from old ones.
For example, in many proof systems for propositional logic, we have the rule of modus ponens:

From a proof of Implies p q and a proof of p, we obtain a proof of q.

We could represent this as follows:

-/

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q

-- so this is a function that given p,q prop, Proof of Implies p q and Proof p -- the axiom states
-- that it exists and is a function returning a proof of q. Meaning q has been proven via the axiom -- given
-- the correct inputs

/-
This approach would provide us with a reasonable way of building assertions and proofs.

Determining that an expression t is a correct proof of assertion p would then simply
be a matter of checking that t has type Proof p.
-/

/-
Some simplifications are possible, however.
To start with, we can avoid writing the term Proof repeatedly by conflating Proof p with p itself.

In other words, whenever we have p : Prop, we can interpret p as a type, namely, the type of its proofs.
We can then read t : p as the assertion that t is a proof of p.


-/

/-
Moreover, once we make this identification, the rules for implication
show that we can pass back and forth between Implies p q and p → q.

In other words, implication between propositions p and q corresponds to having a function that takes any element of p to an element of q.
As a result, the introduction of the connective Implies is entirely redundant:
we can use the usual function space constructor p → q from dependent type theory as our notion of implication.

-/
 -- as seen by def Implies (α : Prop) (β: Prop): Prop := α → β

 /-
 This is the approach followed in the Calculus of Constructions, and hence in Lean as well.
 The fact that the rules for implication in a proof system for natural deduction correspond
 exactly to the rules governing abstraction and application for functions is an instance of the Curry-Howard isomorphism,
 sometimes known as the propositions-as-types paradigm.

  In fact, the type Prop is syntactic sugar for Sort 0, the very bottom of the type hierarchy described in the last chapter.
  Moreover, Type u is also just syntactic sugar for Sort (u+1). Prop has some special features, but like the other type universes,
  it is closed under the arrow constructor: if we have p q : Prop, then p → q : Prop.
 -/

 /-
There are at least two ways of thinking about propositions as types.
To some who take a constructive view of logic and mathematics,
this is a faithful rendering of what it means to be a proposition:
a proposition p represents a sort of data type, namely, a specification of the type of data that constitutes a proof.
A proof of p is then simply an object t : p of the right type.

Those not inclined to this ideology can view it, rather, as a simple coding trick.
To each proposition p we associate a type that is empty if p is false(? not yet proven?) and has a single element,
say *, if p is true. In the latter case, let us say that (the type associated with) p is inhabited.

It just so happens that the rules for function application and abstraction can conveniently
help us keep track of which elements of Prop are inhabited.
So constructing an element t : p tells us that p is indeed true.
You can think of the inhabitant of p as being the "fact that p is true."

A proof of p → q uses "the fact that p is true" to obtain "the fact that q is true."

Indeed, if p : Prop is any proposition, Lean's kernel treats any two elements t1 t2 : p as being definitionally equal,
much the same way as it treats (fun x => t) s and t[s/x] as definitionally equal.

This is known as proof irrelevance, and is consistent with the interpretation in the last paragraph.
It means that even though we can treat proofs t : p as ordinary objects in the language of dependent type theory,
they carry no information beyond the fact that p is true.

The two ways we have suggested thinking about the propositions-as-types paradigm differ in a fundamental way.
From the constructive point of view, proofs are abstract mathematical objects that are denoted by suitable expressions in dependent type theory.
In contrast, if we think in terms of the coding trick described above, then the expressions themselves do not denote anything interesting.
Rather, it is the fact that we can write them down and check that they are well-typed that ensures that the proposition in question is true.
In other words, the expressions themselves are the proofs.

In the exposition below, we will slip back and forth between these two ways of talking,
at times saying that an expression "constructs" or "produces" or "returns" a proof of a proposition,
and at other times simply saying that it "is" such a proof.

This is similar to the way that computer scientists occasionally blur the distinction between syntax and semantics by saying,
at times, that a program "computes" a certain function, and at other times speaking as though the program "is" the function in question.

In any case, all that really matters is the bottom line. To formally express a mathematical assertion in the language of dependent type theory, we need to exhibit a term p : Prop. To prove that assertion, we need to exhibit a term t : p. Lean's task, as a proof assistant, is to help us to construct such a term, t, and to verify that it is well-formed and has the correct type.
 -/
