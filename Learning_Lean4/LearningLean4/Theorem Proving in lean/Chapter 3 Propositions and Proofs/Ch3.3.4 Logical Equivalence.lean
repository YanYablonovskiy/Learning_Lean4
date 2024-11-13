/-
The expression Iff.intro h1 h2 produces a proof of p ↔ q from h1 : p → q and h2 : q → p.
The expression Iff.mp h produces a proof of p → q from h : p ↔ q.

Similarly, Iff.mpr h produces a proof of q → p from h : p ↔ q.
Here is a proof of p ∧ q ↔ q ∧ p:
-/

-- my version
--v1
#check And.intro
variable (p q r: Prop)
example: p ∧ q ↔ q ∧ p := Iff.intro (fun hpnq: p ∧ q => And.intro (hpnq.right) (hpnq.left)) (fun (hqnp: q ∧ p) => ⟨hqnp.right,hqnp.left⟩)

--TPIL


theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

/-
We can use the anonymous constructor notation to construct a proof of p ↔ q from proofs of the forward and backward directions,
and we can also use . notation with mp and mpr.

The previous examples can therefore be written concisely as follows:
-/


theorem and_swap_short : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap_short p q).mp h
