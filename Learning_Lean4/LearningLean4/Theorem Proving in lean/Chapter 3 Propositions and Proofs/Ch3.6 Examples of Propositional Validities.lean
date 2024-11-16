/-
Lean's standard library contains proofs of many valid statements of propositional logic,
all of which you are free to use in proofs of your own. The following list includes a number of
common identities.

Commutativity:

-/
variable (p q r: Prop)
#check p ∧ q ↔ q ∧ p
#check p ∨ q ↔ q ∨ p

variable (k: Type)
#check (x: Type) → k -- Type 1
#check (w:Prop) → p --impredicative prop

/-Associativity: -/

#check (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
#check (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)

/- Distributivity: -/

#check p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
#check p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)

/-Other properties: -/

#check (p → (q → r)) ↔ (p ∧ q → r)
#check ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)
#check ¬(p ∨ q) ↔ ¬p ∧ ¬q
#check ¬p ∨ ¬q → ¬(p ∧ q)
#check ¬(p ∧ ¬p)
#check p ∧ ¬q → ¬(p → q)
#check ¬p → (p → q)
#check (¬p ∨ q) → (p → q)
#check p ∨ False ↔ p
#check p ∧ False ↔ False
#check ¬(p ↔ ¬p)
#check (p → q) → (¬q → ¬p)

/-
These require classical reasoning:
-/

#check (p → r ∨ q) → ((p → r) ∨ (p → q))
#check ¬(p ∧ q) → ¬p ∨ ¬q
#check ¬(p → q) → p ∧ ¬q
#check (p → q) → (¬p ∨ q)
#check (¬q → ¬p) → (p → q)
#check p ∨ ¬p
#check (((p → q) → p) → p)

/-
The sorry identifier magically produces a proof of anything, or provides an object of any data type at all.
Of course, it is unsound as a proof method -- for example, you can use it to prove False -- and Lean produces
severe warnings when files use or import theorems which depend on it.

But it is very useful for building long proofs incrementally.

Start writing the proof from the top down, using sorry to fill in subproofs. Make sure Lean accepts the term with all the sorry's;
if not, there are errors that you need to correct.

Then go back and replace each sorry with an actual proof, until no more remain.

-/

example {p q r: Prop}:p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
have h₁: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := fun (h: p ∧ (q ∨ r)) => --using or elim along with p from h
Or.elim (h.2) (fun (h₂: q) => Or.intro_left (p ∧ r) (And.intro h.1 h₂)) (fun (h₃: r) => Or.intro_right (p ∧ q) (And.intro h.1 h₃))
have h₄: (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := fun (hpqpr:(p ∧ q) ∨ (p ∧ r)) =>
Or.elim (hpqpr) (λ (hpq:p ∧ q) => And.intro hpq.1 (Or.intro_left r hpq.2)) (λ (hpr:p ∧ r) => And.intro hpr.1 (Or.intro_right q hpr.2))
show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) from Iff.intro h₁ h₄

/-
Here is another useful trick. Instead of using sorry, you can use an underscore _ as a placeholder.

Recall this tells Lean that the argument is implicit, and should be filled in automatically.
If Lean tries to do so and fails, it returns with an error message "don't
know how to synthesize placeholder," followed by the type of the term it is expecting,
and all the objects and hypotheses available in the context.

In other words, for each unresolved placeholder, Lean reports the subgoal that needs to be
filled at that point. You can then construct a proof by incrementally filling in these placeholders.

For reference, here are two sample proofs of validities taken from the list above.
-/
open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
