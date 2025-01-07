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

--dont need to be axioms


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
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of a
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a :=
  rfl


/-
The four constants, Quot, Quot.mk, Quot.ind, and Quot.lift in and of themselves are not
very strong.

You can check that the Quot.ind is satisfied if we take Quot r to be simply α,
and take Quot.lift to be the identity function (ignoring h).

For that reason, these four constants are not viewed as additional axioms.

They are, like inductively defined types and the associated constructors and recursors,
viewed as part of the logical framework.

What makes the Quot construction into a bona fide quotient is the following
additional axiom:

-/
namespace ex
universe u
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b

/-

This is the axiom that asserts that any two elements of α that are related by r become
identified in the quotient.

If a theorem or definition makes use of Quot.sound, it will show up in the #print axioms
command.

-/


/-
Of course, the quotient construction is most commonly used in situations when r is an
equivalence relation.

Given r as above, if we define r' according to the rule r' a b iff Quot.mk r a = Quot.mk r b,
then it's clear that r' is an equivalence relation.

Indeed, r' is the kernel of the function a ↦ quot.mk r a.

The axiom Quot.sound says that r a b implies r' a b.

Using Quot.lift and Quot.ind, we can show that r' is the smallest
equivalence relation containing r, in the sense that if r'' is any equivalence
relation containing r, then r' a b implies r'' a b.

In particular, if r was an equivalence relation to start with, then for
all a and b we have r a b iff r' a b.
-/

/-
To support this common use case, the standard library defines the notion of a setoid,
which is simply a type with an associated equivalence relation:
-/

class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid

/-
Given a type α, a relation r on α, and a proof p that r is an equivalence relation,
we can define Setoid.mk r p as an instance of the setoid class.
-/
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r


/-
The constants Quotient.mk, Quotient.ind, Quotient.lift, and Quotient.sound are nothing
more than the specializations of the corresponding elements of Quot.

The fact that type class inference can find the setoid associated to a type α brings
a number of benefits.

First, we can use the notation a ≈ b (entered with \approx) for Setoid.r a b,
where the instance of Setoid is implicit in the notation Setoid.r.

We can use the generic theorems Setoid.refl, Setoid.symm, Setoid.trans
to reason about the relation.

Specifically with quotients we can use the generic notation ⟦a⟧ for Quot.mk Setoid.r
where the instance of Setoid is implicit in the notation Setoid.r,
as well as the theorem Quotient.exact:

-/


end ex

universe u
#check (@Quotient.exact :
         ∀ {α : Sort u} {s : Setoid α} {a b : α},
           Quotient.mk s a = Quotient.mk s b → a ≈ b)

/-
Together with Quotient.sound, this implies that the elements of the quotient correspond exactly to the equivalence classes of elements in α.

Recall that in the standard library, α × β represents the Cartesian product of the types
α and β.

To illustrate the use of quotients, let us define the type of unordered pairs of
elements of a type α as a quotient of the type α × α.

First, we define the relevant equivalence relation:
-/

private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv

/-
The next step is to prove that eqv is in fact an equivalence relation, which is to say,
it is reflexive, symmetric and transitive.

We can prove these three facts in a convenient and readable way by using dependent pattern
matching to perform case-analysis and break the hypotheses into pieces that are then
reassembled to produce the conclusion.

-/

private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

/-
Now that we have proved that eqv is an equivalence relation, we can construct a
Setoid (α × α), and use it to define the type UProd α of unordered pairs.
-/


instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd

/-
Notice that we locally define the notation {a₁, a₂} for unordered pairs as
Quotient.mk (a₁, a₂).

This is useful for illustrative purposes, but it is not a good idea in general,
since the notation will shadow other uses of curly brackets, such as for records and sets.

We can easily prove that {a₁, a₂} = {a₂, a₁} using Quot.sound, since we have
(a₁, a₂) ~ (a₂, a₁).


-/

theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)


/-
To complete the example, given a : α and u : uprod α, we define the proposition a ∈ u
which should hold if a is one of the elements of the unordered pair u.

First, we define a similar proposition mem_fn a u on (ordered) pairs; then we show
that mem_fn respects the equivalence relation eqv with the lemma mem_respects.

This is an idiom that is used extensively in the Lean standard library.
-/
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving mem_respects
private theorem mem_swap {a : α} :
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h


private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by simp_all; apply propext_iff.mp; apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h

/-
For convenience, the standard library also defines Quotient.lift₂ for lifting
binary functions, and Quotient.ind₂ for induction on two variables.

We close this section with some hints as to why the quotient construction implies
function extensionality.

It is not hard to show that extensional equality on the (x : α) → β x is an equivalence relation,
and so we can consider the type extfun α β of functions "up to equivalence."

Of course, application respects that equivalence in the sense that if f₁ is equivalent to f₂, then f₁ a is equal to f₂ a.

Thus application gives rise to a function extfun_app : extfun α β → (x : α) → β x.

But for every f, extfun_app ⟦f⟧ is definitionally equal to fun x => f x, which is in turn definitionally
equal to f.

So, when f₁ and f₂ are extensionally equal, we have the following chain of equalities:

<    f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂ >

As a result, f₁ is equal to f₂.
-/
