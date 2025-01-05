/-
Quotients:

Let α be any type, and let r be an equivalence relation on α.

It is mathematically common to form the "quotient" α / r, that is, the type of
elements of α "modulo" r.

Set theoretically, one can view α / r as the set of equivalence classes of α modulo r.

If f : α → β is any function that respects the equivalence relation in the sense
that for every x y : α, r x y implies f x = f y, then f "lifts" to a function
f' : α / r → β defined on each equivalence class ⟦x⟧ by f' ⟦x⟧ = f x.

Lean's standard library extends the Calculus of Constructions with additional
constants that perform exactly these constructions, and installs this last
equation as a definitional reduction rule.

In its most basic form, the quotient construction does not even require r to be an
equivalence relation. The following constants are built into Lean:
-/

namespace ex

universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → ((q : Quot r) → β q)

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → (Quot r → β)

/-

The first one forms a type Quot r given a type α by any binary relation r on α.

The second maps α to Quot α, so that if r : α → α → Prop and a : α, then Quot.mk r a
is an element of Quot r.

The third principle, Quot.ind, says that every element of Quot.mk r a is of this form.

As for Quot.lift, given a function f : α → β, if h is a proof that f respects the relation
r, then Quot.lift f h is the corresponding function on Quot r.

The idea is that for each element a in α, the function Quot.lift f h maps Quot.mk r a
(the r-class containing a) to f a, wherein h shows that this function is well defined.

In fact, the computation principle is declared as a reduction rule, as the proof below
makes clear.

-/

end ex
