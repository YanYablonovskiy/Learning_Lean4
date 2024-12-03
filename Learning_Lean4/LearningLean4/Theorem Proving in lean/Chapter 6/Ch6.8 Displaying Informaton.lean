/-
There are a number of ways in which you can query Lean for information about its
current state and the objects and theorems that are available in the current context.

You have already seen two of the most common ones, #check and #eval.

Remember that #check is often used in conjunction with the @ operator,
which makes all of the arguments to a theorem or definition explicit.

In addition, you can use the #print command to get information about any identifier.

If the identifier denotes a definition or theorem, Lean prints the type
of the symbol, and its definition.

If it is a constant or an axiom, Lean indicates that fact, and shows the type.
-/
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo
