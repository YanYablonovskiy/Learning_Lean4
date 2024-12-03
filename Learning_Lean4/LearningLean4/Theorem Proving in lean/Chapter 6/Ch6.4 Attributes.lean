/-
The main function of Lean is to translate user input to formal expressions that are checked by the kernel for
correctness and then stored in the environment for later use.

But some commands have other effects on the environment, either assigning attributes to objects in the environment,
defining notation, or declaring instances of type classes, as described in Chapter Type Classes.

Most of these commands have global effects, which is to say, they remain in effect not only in the current file,
but also in any file that imports it.

However, such commands often support the local modifier, which indicates that they only have effect
until the current section or namespace is closed, or until the end of the current file.

In Section Using the Simplifier, we saw that theorems can be annotated with the [simp] attribute,
which makes them available for use by the simplifier.

The following example defines the prefix relation on lists, proves that this relation is reflexive,
and assigns the [simp] attribute to that theorem.
-/

def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩ --showing its a prefix of itself, by showing as + [] = as

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

/-
The simplifier then proves isPrefix [1, 2, 3] [1, 2, 3] by rewriting it to True.

One can also assign the attribute any time after the definition takes place:
-/
theorem List.isPrefix_self' (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self'

/-
In all these cases, the attribute remains in effect in any file that imports the one in which the declaration occurs.

Adding the local modifier restricts the scope:
-/

section

theorem List.isPrefix_self'' (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

-- Error:
-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--  simp

/-
For another example, we can use the instance command to assign the notation ≤ to the isPrefix relation.

That command, which will be explained in Chapter Type Classes, works by assigning an [instance]
attribute to the associated definition.
-/
instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_selfle (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

/-
That assignment can also be made local:
-/
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe
-- and done after the def this time
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩

/-
In Section Notation below, we will discuss Lean's mechanisms for defining notation,
and see that they also support the local modifier.

However, in Section Setting Options, we will discuss Lean's mechanisms for setting options,
which does not follow this pattern: options can only be set locally, which is to say,
their scope is always restricted to the current section or current file.
-/
