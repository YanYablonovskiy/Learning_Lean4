import Mathlib.Data.Set.Defs
/-
Coercions using Type Classes:

The most basic type of coercion maps elements of one type to another.

For example, a coercion from Nat to Int allows us to view any
element n : Nat as an element of Int.

But some coercions depend on parameters; for example, for any type α,
we can view any element as : List α as an element of Set α,
namely, the set of elements occurring in the list.

The corresponding coercion is defined on the "family" of
types List α, parameterized by α.

Lean allows us to declare three kinds of coercions:

⬝ from a family of types to another family of types
⬝ from a family of types to the class of sorts
⬝ from a family of types to the class of function types

The first kind of coercion allows us to view any element of a member of the source family
as an element of a corresponding member of the target family.

The second kind of coercion allows us to view any element of a
member of the source family as a type.

The third kind of coercion allows us to view any element
of the source family as a function.

Let us consider each of these in turn.

In Lean, coercions are implemented on top of the type class resolution
framework.

We define a coercion from α to β by declaring an instance of Coe α β.

For example, we can define a coercion from Bool to Prop as follows:
-/

instance : Coe Bool Prop where
  coe b := b = true

/-
This enables us to use boolean terms in if-then-else expressions:
-/
#eval if true then 5 else 3
#eval if false then 5 else 3

/-
We can define a coercion from List α to Set α as follows:
-/
universe u
variable (α: Type u)


def List.toSet : List α → Set α
  | []    => {}
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}
#check s ∪ [2, 3]
-- s ∪ List.toSet [2, 3] : Set Nat
/-
We can use the notation ↑ to force a coercion to be introduced in
a particular place.

It is also helpful to make our intent clear, and work around limitations
of the coercion resolution system.
-/

#check let x := ↑[2, 3]; s ∪ x
-- let x := List.toSet [2, 3]; s ∪ x : Set Nat
#check let x := [2, 3]; s ∪ x
-- let x := [2, 3]; s ∪ List.toSet x : Set Nat

/-
Dependent Coercion:

Lean also supports dependent coercions using the type class CoeDep.

For example, we cannot coerce arbitrary propositions to Bool, only
the ones that implement the Decidable typeclass.

-/
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p

/-
Lean will also chain (non-dependent) coercions as necessary.

Actually, the type class CoeT is the transitive closure of Coe.

Let us now consider the second kind of coercion.

By the class of sorts, we mean the collection of universes Type u.

A coercion of the second kind is of the form:


    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u

where F is a family of types as above.

This allows us to write s : t whenever t is of type F a1 ... an.

In other words, the coercion allows us to view the elements
of F a1 ... an as types.

This is very useful when defining algebraic structures in which
one component, the carrier of the structure, is a Type.

For example, we can define a semigroup as follows:
-/
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b

/-
In other words, a semigroup consists of a type, carrier, and
a multiplication, mul, with the property that the multiplication
is associative.

The instance command allows us to write a * b instead of
Semigroup.mul S a b whenever we have a b : S.carrier;
notice that Lean can infer the argument S from the types of a and b.

The function Semigroup.carrier maps the class Semigroup to the
sort Type u:
-/

#check Semigroup.carrier
/-
If we declare this function to be a coercion, then whenever we have a
semigroup S : Semigroup, we can write a : S instead of a : S.carrier:
-/

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c

/-
It is the coercion that makes it possible to write (a b c : S).

Note that, we define an instance of CoeSort Semigroup (Type u)
instead of Coe Semigroup (Type u).

By the class of function types, we mean the collection
of Pi types (z : B) → C. The third kind of coercion has the form:
-/

/-
    c : (x1 : A1) → ... → (xn : An) → (y : F x1 ... xn) → (z : B) → C
-/

/-
where F is again a family of types and B and C can depend on x1, ..., xn, y.

This makes it possible to write t s whenever t is an element of
F a1 ... an.

In other words, the coercion enables us to view elements of F a1 ... an as functions.

Continuing the example above, we can define the notion of a morphism between
semigroups S1 and S2.

That is, a function from the carrier of S1 to the carrier of S2
(note the implicit coercion) that respects the multiplication.

The projection morphism.mor takes a morphism to the underlying function:
-/
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor

/-
As a result, it is a prime candidate for the third type of coercion.
-/

instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]

/-
With the coercion in place, we can write f (a * a * a) instead of f.mor (a * a * a).

When the Morphism, f, is used where a function is expected, Lean inserts
the coercion.

Similar to CoeSort, we have yet another class CoeFun for this class
of coercions.

The field F is used to specify the function type we are coercing to.

This type may depend on the type we are coercing from. (not in this case)
-/
