/-
Mutual and Nested Inductive Types:

We now consider two generalizations of inductive types that are often useful,
which Lean supports by "compiling" them down to the more primitive kinds of
inductive types described above.

In other words, Lean parses the more general definitions, defines auxiliary inductive types
based on them, and then uses the auxiliary types to define the ones we really want.

Lean's equation compiler, described in the next chapter, is needed to make use of
these types effectively.

Nonetheless, it makes sense to describe the declarations here,
because they are straightforward variations on ordinary inductive definitions.

First, Lean supports mutually defined inductive types.

The idea is that we can define two (or more) inductive types at the same time,
where each one refers to the other(s).
-/

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

/-
In this example, two types are defined simultaneously: a natural number n is Even if it is 0 or one more than an Odd number,
and Odd if it is one more than an Even number.

In the exercises below, you are asked to spell out the details.

A mutual inductive definition can also be used to define the notation of a
finite tree with nodes labelled by elements of α:
-/

mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end

/-
With this definition, one can construct an element of Tree α by giving an element
of α together with a list of subtrees, possibly empty.

The list of subtrees is represented by the type TreeList α, which is defined to be either
the empty list, nil, or the cons of a tree and an element of TreeList α.

This definition is inconvenient to work with, however.

It would be much nicer if the list of subtrees were given by
the type List (Tree α), especially since Lean's library contains a
number of functions and theorems for working with lists.

One can show that the type TreeList α is isomorphic to List (Tree α),
but translating results back and forth along this isomorphism is tedious.

In fact, Lean allows us to define the inductive type we really want:
-/

inductive Tree_s (α : Type u) where
  | mk : α → List (Tree_s α) → Tree_s α

/-
This is known as a nested inductive type.

It falls outside the strict specification of an inductive type given in the last section
because Tree does not occur strictly positively among the arguments to mk, but, rather,
nested inside the List type constructor.

Lean then automatically builds the isomorphism between TreeList α and List (Tree α)
in its kernel, and defines the constructors for Tree in terms of the isomorphism.
-/
