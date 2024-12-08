/-
Axiomatic Details:

We have described inductive types and their syntax through examples.

This section provides additional information for those interested in the axiomatic foundations.

We have seen that the constructor to an inductive type takes parameters --- intuitively, the arguments
that remain fixed throughout the inductive construction --- and indices, the arguments parameterizing the
family of types that is simultaneously under construction.

Each constructor should have a type, where the argument types are built up from previously defined types,
the parameter and index types, and the inductive family currently being defined.

The requirement is that if the latter is present at all, it occurs only strictly positively.

This means simply that any argument to the constructor in which it occurs is a dependent arrow type
in which the inductive type under definition occurs only as the resulting type, where the indices
are given in terms of constants and previous arguments.

Since an inductive type lives in Sort u for some u, it is reasonable to ask which universe
levels u can be instantiated to.

 Each constructor c in the definition of a family C of inductive types is of the form
-/

/-
  c : (a : α) → (b : β[a]) → C a p[a,b]
-/

/-
where a is a sequence of data type parameters, b is the sequence of arguments to the constructors,
and p[a, b] are the indices, which determine which element of the inductive family the construction inhabits.

(Note that this description is somewhat misleading, in that the arguments to the constructor
can appear in any order as long as the dependencies make sense.)

The constraints on the universe level of C fall into two cases, depending
on whether or not the inductive type is specified to land in Prop (that is, Sort 0).
-/

/-
Let us first consider the case where the inductive type is not specified to land in Prop.

Then the universe level u is constrained to satisfy the following:
-/
/-
For each constructor c as above, and each βk[a] in the sequence β[a], if βk[a] : Sort v,
we have u ≥ v.
-/

/-
In other words, the universe level u is required to be at least as large as the universe
level of each type that represents an argument to a constructor.
-/

/-
When the inductive type is specified to land in Prop, there are no constraints on the
universe levels of the constructor arguments.

But these universe levels do have a bearing on the elimination rule.

Generally speaking, for an inductive type in Prop, the motive of the elimination rule
is required to be in Prop.

There is an exception to this last rule: we are allowed to eliminate from
an inductively defined Prop to an arbitrary Sort when there is only one constructor
and each constructor argument is either in Prop or an index.

The intuition is that in this case the elimination does not make
use of any information that is not already given by the mere fact that
the type of argument is inhabited.

This special case is known as singleton elimination.

We have already seen singleton elimination at play in applications of Eq.rec,
the eliminator for the inductively defined equality type.

We can use an element h : Eq a b to cast an element t' : p a to p b even when
p a and p b are arbitrary types, because the cast does not produce new data;
it only reinterprets the data we already have.

Singleton elimination is also used with heterogeneous equality and well-founded recursion,
which will be discussed in a Chapter Induction and Recursion.
-/
