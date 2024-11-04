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

def Proof (α : Prop): Type := Sort 0 -- This isnt actually the way Proof works, it will likely be a new type
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
