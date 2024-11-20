/-
We have seen that keywords like fun, have, and show make it possible to write formal proof
terms that mirror the structure of informal mathematical proofs.

In this section, we discuss some additional features of the proof language that
are often convenient.

To start with, we can use anonymous "have" expressions to introduce an auxiliary goal
without having to label it.

We can refer to the last expression introduced in this way using the keyword this:
-/
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

--my versions

example : f 0 ≤ f 3 := by
 repeat apply Nat.le_trans _ (h _)
 apply (Nat.le_of_eq (Eq.refl (f 0)))

/-
Often proofs move from one fact to the next, so this can be effective
in eliminating the clutter of lots of labels.

When the goal can be inferred, we can also ask Lean instead to fill in
the proof by writing by assumption:
-/

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

/-
This tells Lean to use the assumption tactic, which, in turn, proves the goal by finding
a suitable hypothesis in the local context.

We will learn more about the assumption tactic in the next chapter.
-/

/-
We can also ask Lean to fill in the proof by writing ‹p›, where p is the proposition whose proof
we want Lean to find in the context. You can type these corner quotes using \f< and \f>, respectively.

The letter "f" is for "French," since the unicode symbols can also be used as French quotation marks.

In fact, the notation is defined in Lean as follows:
-/

--notation "‹" p "›" => show p by assumption

/-
This approach is more robust than using by assumption, because the type of the assumption that needs to be inferred is given explicitly.

It also makes proofs more readable. Here is a more elaborate example:
-/
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans (show f 1 ≥ f 2 by assumption) (show f 0 ≥ f 1 by assumption)
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

-- using antisym of ≤ to show =

/-
Keep in mind that you can use the French quotation marks in this way to refer to anything
in the context, not just things that were introduced anonymously.

Its use is also not limited to propositions, though using it for data is somewhat odd:
-/
example (n : Nat) : Nat := ‹Nat›

/-
Later, we show how you can extend the proof language using the Lean macro system.
-/
