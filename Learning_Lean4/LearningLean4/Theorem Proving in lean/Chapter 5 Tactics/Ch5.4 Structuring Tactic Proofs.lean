/-
Tactics often provide an efficient way of building a proof, 
but long sequences of instructions can obscure the structure of the argument. 

In this section, we describe some means that help provide structure to a tactic-style proof, 
making such proofs more readable and robust.

One thing that is nice about Lean's proof-writing syntax is that it is possible 
to mix term-style and tactic-style proofs, and pass between the two freely. 

For example, the tactics apply and exact expect arbitrary terms, 
which you can write using have, show, and so on. 

Conversely, when writing an arbitrary Lean term, you can always invoke 
the tactic mode by inserting a by block. 

The following is a somewhat toy example:
-/
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h -- introducing h:p ∧ (q ∨ r)
  exact -- using exact block; to construct (p ∧ q) ∨ (p ∧ r)
    have hp : p := h.left
    have hqr : q ∨ r := h.right --
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

/-
The following is a more natural example:
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with --we use cases, and h.right
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

/-
In fact, there is a show tactic, which is similar to the show expression in a proof term. 

It simply declares the type of the goal that is about to be solved, while remaining in tactic mode.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro --two cases; mp and mpr
  . intro h --h:p ∧ (q ∨ r) for p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
    cases h.right with --cases on q ∨ r
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h --h:(p ∧ q) ∨ (p ∧ r)
    cases h with
    | inl hpq => --h: p ∧ q; first case
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩ --And intro, using p from hpq.left; and Or.inl having q
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

/-
The show tactic can actually be used to rewrite a goal to something definitionally equivalent:
-/

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

/-
There is also a have tactic, which introduces a new subgoal, just as 
when writing proof terms:
-/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
