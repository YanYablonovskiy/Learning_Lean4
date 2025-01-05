/-
Function Extensionality:

Similar to propositional extensionality, function extensionality asserts
that any two functions of type (x : α) → β x that agree on all their
inputs are equal:
-/

namespace ex

universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

/-
The statement is:

(∀ (x : α), f x = g x)
         → f = g)
-/


#print funext


/-
From a classical, set-theoretic perspective, this is exactly what it
means for two functions to be equal.

This is known as an "extensional" view of functions.

From a constructive perspective, however, it is sometimes more natural
to think of functions as algorithms, or computer programs, that are
presented in some explicit way.

It is certainly the case that two computer programs can compute the same
answer for every input despite the fact that they are syntactically
quite different.

In much the same way, you might want to maintain a view of functions
that does not force you to identify two functions that have the same
input / output behavior.

This is known as an "intensional" view of functions.

In fact, function extensionality follows from the existence of
quotients, which we describe in the next section.

In the Lean standard library, therefore, funext is thus proved from
the quotient construction.

Suppose that for α : Type we define
the Set α := α → Prop to denote the type of subsets of α,
essentially identifying subsets with predicates.

By combining funext and propext, we obtain an extensional theory of
such sets:
-/


def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))


--since sets are essentially functions


/-
We can then proceed to define the empty set and set intersection,
for example, and prove set identities:
-/
def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h) --from a ∩ a to a
    (fun h => ⟨h, h⟩) --from a to a ∩ a

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h) --from a ∩ ∅ to ∅
    (fun h => False.elim h)--from ∅ to a ∩ ∅

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)

/-
The following is an example of how function extensionality blocks
computation inside the Lean kernel:
-/


end Set
end ex
