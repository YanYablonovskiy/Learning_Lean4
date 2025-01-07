/-
Choice
To state the final axiom defined in the standard library, we need the Nonempty type,
which is defined as follows:
-/
namespace ex

class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α

/-
Because Nonempty α has type Prop and its constructor contains data, it can only eliminate
to Prop.

In fact, Nonempty α is equivalent to ∃ x : α, True:
-/

example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)

/-
Our axiom of choice is now expressed simply as follows:
-/
universe u
axiom choice {α : Sort u} : Nonempty α → α

/-
Given only the assertion h that α is nonempty, choice h magically produces an element of α.

Of course, this blocks any meaningful computation: by the interpretation of Prop,
h contains no information at all as to how to find such an element.

This is found in the Classical namespace, so the full name of the theorem is
Classical.choice.

The choice principle is equivalent to the principle of indefinite description,
which can be expressed with subtypes as follows:
-/
noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
                                        (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

/-
Because it depends on choice, Lean cannot generate bytecode for indefiniteDescription,
and so requires us to mark the definition as noncomputable.

Also in the Classical namespace, the function choose and the property
choose_spec decompose the two parts of the output of indefiniteDescription:
-/
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property

/-
The choice principle also erases the distinction between the property of being
Nonempty and the more constructive property of being Inhabited:
-/
end ex
open Classical

noncomputable def inhabited_of_nonempty : Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)

/-
In the next section, we will see that propext, funext, and choice, taken together,
imply the law of the excluded middle and the decidability of all propositions.

Using those, one can strengthen the principle of indefinite description as follows:
-/
universe u
#check (@strongIndefiniteDescription :
         {α : Sort u} → (p : α → Prop)
         → Nonempty α → {x // (∃ (y : α), p y) → p x}) --can find a type x using choice

/-
Assuming the ambient type α is nonempty, strongIndefiniteDescription p produces an
element of α satisfying p if there is one.

The data component of this definition is conventionally known as
Hilbert's epsilon function:
-/
#check (@epsilon :
         {α : Sort u} → [Nonempty α]
         → (α → Prop) → α)

#check (@epsilon_spec :
         ∀ {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y),
           p (@epsilon _ (nonempty_of_exists hex) p))
