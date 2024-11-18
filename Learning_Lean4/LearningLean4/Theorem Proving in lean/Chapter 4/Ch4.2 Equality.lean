/-
Let us now turn to one of the most fundamental relations defined in Lean's library, namely, the equality relation.

In Chapter Inductive Types, we will explain how equality is defined from the primitives of Lean's logical framework.

In the meanwhile, here we explain how to use it.

Of course, a fundamental property of equality is that it is an equivalence relation:
-/
#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
