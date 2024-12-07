/-
Inductively defined types can live in any type universe, including the bottom-most one,
Prop.

In fact, this is exactly how the logical connectives are defined.
-/
namespace Hidden

inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

--

inductive Or_2 (a b : Prop) where --can omit :Prop
  | inl : a → Or_2 a b
  | inr : b → Or_2 a b

/-
You should think about how these give rise to the introduction and elimination rules that you have already seen.

There are rules that govern what the eliminator of an inductive type can eliminate to, that is, what kinds of types can be the target of a recursor.

Roughly speaking, what characterizes inductive types in Prop is that one can only eliminate to other types in Prop.

This is consistent with the understanding that if p : Prop, an element hp : p carries no data.

There is a small exception to this rule, however, which we will discuss below, in Section Inductive Families.
-/

/-
Even the existential quantifier is inductively defined:
-/

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

/-
Keep in mind that the notation ∃ x : α, p is syntactic sugar for Exists (fun x : α => p).

The definitions of False, True, And, and Or are perfectly analogous to the definitions of Empty, Unit, Prod, and Sum.

The difference is that the first group yields elements of Prop, and the second yields elements of Type u for some u.

In a similar way, ∃ x : α, p is a Prop-valued variant of Σ x : α, p.

This is a good place to mention another inductive type, denoted {x : α // p}, which is sort of a
hybrid between ∃ x : α, P and Σ x : α, P.
-/

#check Sigma
#print Sigma

inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p --like exists, but many exists at once

/-
In fact, in Lean, Subtype is defined using the structure command:
-/
structure Subtype_1 {α : Sort u} (p : α → Prop) where
  val : α
  property : p val

/-
The notation {x : α // p x} is syntactic sugar for Subtype (fun x : α => p x).

It is modeled after subset notation in set theory: the idea is that
{x : α // p x} denotes the collection of elements of α that have property p.
-/
