/-
Propositional Extensionality:

Propositional extensionality is the following axiom:
-/
namespace ex
axiom propext {a b : Prop} : (a ↔ b) → a = b

/-
It asserts that when two propositions imply one another, they are actually
equal.

This is consistent with set-theoretic interpretations in which any element
a : Prop is either empty or the singleton set {*}, for some distinguished
element *.

The axiom has the effect that equivalent propositions can be substituted
for one another in any context:
-/


theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

end ex
