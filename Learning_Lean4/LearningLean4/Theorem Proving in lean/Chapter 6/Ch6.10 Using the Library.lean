/-
To use Lean effectively you will inevitably need to make use of definitions and theorems in the library.

Recall that the import command at the beginning of a file imports previously compiled results from other files,
and that importing is transitive; if you import Foo and Foo imports Bar, then the definitions and theorems from
Bar are available to you as well.

But the act of opening a namespace, which provides shorter names, does not carry over.

In each file, you need to open the namespaces you wish to use.

In general, it is important for you to be familiar with the library and its contents,
so you know what theorems, definitions, notations, and resources are available to you.

Below we will see that Lean's editor modes can also help you find things you need,
but studying the contents of the library directly is often unavoidable.

Lean's standard library can be found online, on GitHub:
-/

 -- https://github.com/leanprover/lean4/tree/master/src/Init

 -- https://github.com/leanprover/std4/tree/main/Std

/-
You can see the contents of these directories and files using GitHub's browser interface.

If you have installed Lean on your own computer, you can find the library in the lean folder,
and explore it with your file manager. Comment headers at the top of each file provide additional information.

Lean's library developers follow general naming guidelines to make it easier to guess the name of a theorem you need,
or to find it using tab completion in editors with a Lean mode that supports this, which is discussed in the next section.

Identifiers are generally camelCase, and types are CamelCase.

For theorem names, we rely on descriptive names where the different components are separated by _s.

Often the name of theorem simply describes the conclusion:
-/
#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ

/-
Remember that identifiers in Lean can be organized into hierarchical namespaces.

For example, the theorem named le_of_succ_le_succ in the namespace Nat has full name Nat.le_of_succ_le_succ,
but the shorter name is made available by the command open Nat (for names not marked as protected).

We will see in Chapter Inductive Types and Chapter Structures and Records that defining structures
and inductive data types in Lean generates associated operations, and these are stored in a
namespace with the same name as the type under definition.

For example, the product type comes with the following operations:
-/
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec

/-
The first is used to construct a pair, whereas the next two, Prod.fst and Prod.snd, project the two elements.

The last, Prod.rec, provides another mechanism for defining functions on a product in terms of a function on the two components.

Names like Prod.rec are protected, which means that one has to use the full name even when the Prod namespace is open.

With the propositions as types correspondence, logical connectives are also instances of inductive types,
and so we tend to use dot notation for them as well:
-/

#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst
