/-

The expression And.intro h1 h2 builds a proof of p ∧ q using proofs h1 : p and h2 : q.
It is common to describe And.intro as the and-introduction rule.
In the next example we use And.intro to create a proof of p → q → p ∧ q.

-/

variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

/-

The example command states a theorem without naming it or storing it in the permanent context.
Essentially, it just checks that the given term has the indicated type.
It is convenient for illustration, and we will use it often.

-/


example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

/-

The expression And.left h creates a proof of p from a proof h : p ∧ q.
Similarly, And.right h is a proof of q.
They are commonly known as the left and right and-elimination rules.

We can now prove p ∧ q → q ∧ p with the following proof term.
-/
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

--math version
example: p ∧ q → q ∧ p :=
  fun (h:p∧q) => And.intro (And.right h) (And.left h)


/-
Notice that and-introduction and and-elimination are similar to the pairing and projection operations for the Cartesian product.

The difference is that given hp : p and hq : q, And.intro hp hq has type p ∧ q : Prop,
while Prod hp hq has type p × q : Type.

The similarity between ∧ and × is another instance of the Curry-Howard isomorphism,
but in contrast to implication and the function space constructor, ∧ and ×
are treated separately in Lean.

With the analogy, however, the proof we have just constructed is similar
to a function that swaps the elements of a pair

-/

--in fact you cant even use × the same way
#check p ∧ q

--#check Prod p q --application type mismatch

variable (a b: Type 1)

#check Prod a b

--#check a ∧ b --application type mismatch

/-
We will see in Chapter Structures and Records that certain types in Lean are structures,
which is to say, the type is defined with a single canonical constructor which builds
an element of the type from a sequence of suitable arguments.

For every p q : Prop, p ∧ q is an example: the canonical way to construct an element is to apply
And.intro to suitable arguments hp : p and hq : q. Lean allows us to use anonymous constructor
notation ⟨arg1, arg2, ...⟩ in situations like these, when the relevant type is an
inductive type and can be inferred from the context.

In particular, we can often write ⟨hp, hq⟩ instead of And.intro hp hq:

-/
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
/-
These angle brackets are obtained by typing \< and \>, respectively.

Lean provides another useful syntactic gadget.

Given an expression e of an inductive type Foo (possibly applied to some arguments),
the notation e.bar is shorthand for Foo.bar e.

This provides a convenient way of accessing functions without opening a namespace.

For example, the following two expressions mean the same thing:



-/
variable (xs : List Nat)

#check List.length xs
#check xs.length
#check (⟨hp, hq⟩ : p ∧ q).1
#check And.left (⟨hp, hq⟩ : p ∧ q)


/-
As a result, given h : p ∧ q, we can write h.left for And.left h and h.right for And.right h.
We can therefore rewrite the sample proof above conveniently as follows:
-/
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

--my versions

example: p ∧ q → q ∧ p :=
 fun (hpnq: p ∧ q) => And.intro (And.right hpnq) (And.left hpnq)

example: p ∧ q → q ∧ p :=
 fun (hpnq: p ∧ q) => And.intro hpnq.right hpnq.left

 /-
There is a fine line between brevity and obfuscation, and omitting information in this way can sometimes
make a proof harder to read.

But for straightforward constructions like the one above, when the type of h and the goal of the construction are salient,
the notation is clean and effective.

It is common to iterate constructions like "And."

Lean also allows you to flatten nested constructors that associate to the right,
so that these two proofs are equivalent:
 -/
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

-- ⟨ ⟩ works for all structures -- inductive types built with conjunction --
-- applying pair by pair i.e ⟨ a ⟨b c⟩ ⟩ =: ⟨ a b c ⟩
/-
This is often useful as well.
-/
