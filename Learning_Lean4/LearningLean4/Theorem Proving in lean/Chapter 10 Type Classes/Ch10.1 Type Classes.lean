/-
Type Classes

Type classes were introduced as a principled way of enabling ad-hoc polymorphism in
functional programming languages.

We first observe that it would be easy to implement an ad-hoc polymorphic function
(such as addition) if the function simply took the type-specific implementation of
addition as an argument and then called that implementation on the remaining arguments.

For example, suppose we declare a structure in Lean to hold implementations of addition.
-/
namespace Ex
structure Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a  --the last 3 being the 'add'
-- Add.add : (...) → (...) → 'add'

/-
In the above Lean code, the field add has type Add.add : {a : Type} → Add a → a → a → a
where the curly braces around the type a mean that it is an implicit argument.

We could implement double by:
-/

def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10 --squaring
-- 100

#eval double { add := Int.add } 10
-- 20

--Should be able to find with add from the type


/-
Note that you can double a natural number n by double { add := Nat.add } n.

Of course, it would be highly cumbersome for users to manually pass the implementations
around in this way.

Indeed, it would defeat most of the potential benefits of ad-hoc polymorphism.

The main idea behind type classes is to make arguments such as Add a implicit,
and to use a database of user-defined instances to synthesize the desired instances
automatically through a process known as typeclass resolution.

In Lean, by changing structure to class in the example above, the type of
Add.add becomes:
-/

class Add' (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → [self : Add a] → a → a → a (Add a x:a b:a)
--                        (here there would be a manual version provided)
/-
where the square brackets indicate that the argument of type Add a is instance implicit,
i.e. that it should be synthesized using typeclass resolution.

This version of add is the Lean analogue of the Haskell
term add :: Add a => a -> a -> a.

Similarly, we can register instances by:
-/
instance : Add' Nat where
  add := Nat.add

instance : Add' Int where
  add := Int.add

instance : Add' Float where
  add := Float.add


/-
Then for n : Nat and m : Nat, the term Add.add n m triggers typeclass resolution with
the goal of Add Nat, and typeclass resolution will synthesize the instance for Nat above.

We can now reimplement double using an instance implicit by:
-/
def double' [Add' a] (x : a) : a :=
  Add'.add x x

#check @double
-- @double : {a : Type} → [inst : Add a] → a → a

#eval double' 10
-- 20

#eval double' (10 : Int)
-- 100

#eval double' (7 : Float)
-- 14.000000

#eval double' (239.0 + 2)
-- 482.000000

/-
In general, instances may depend on other instances in complicated ways.

For example, you can declare an (anonymous) instance stating that if a has addition,
then Array a has addition:
-/

instance [Add' a] : Add (Array a) where
  add x y := Array.zipWith x y (Add'.add)
end Ex


instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (· + ·)

/-
Note that (· + ·) is notation for fun x y => x + y in Lean.
-/


/-
The example above demonstrates how type classes are used to overload notation.

Now, we explore another application. We often need an arbitrary element of a given type.

Recall that types may not have any elements in Lean.

It often happens that we would like a definition to return an arbitrary element in a
"corner case."

For example, we may like the expression head xs to be of type a when xs is of type List a.

Similarly, many theorems hold under the additional assumption that a type is not empty.

For example, if a is a type, exists x : a, x = x is true only if a is not empty.

The standard library defines a type class Inhabited to enable type class inference
to infer a "default" element of an inhabited type.

Let us start with the first step of the program above, declaring an appropriate class:
-/

namespace ex

class Inhabited (a : Type u) where
  default : a --a term of type a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a



/-
Note Inhabited.default doesn't have any explicit arguments.
-/

/-
An element of the class Inhabited a is simply an expression of the form Inhabited.mk x, for some element x : a. 

The projection Inhabited.default will allow us to "extract" such an element of a from an element of Inhabited a. 

Now we populate the class with some instances:
-/
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true


end ex

