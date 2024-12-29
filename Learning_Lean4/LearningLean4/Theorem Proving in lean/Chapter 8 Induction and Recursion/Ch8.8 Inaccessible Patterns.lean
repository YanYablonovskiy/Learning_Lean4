-- Chapter 8.8 Inaccessible Patterns

/-
Sometimes an argument in a dependent matching pattern is not essential to the definition,
but nonetheless has to be included to specialize the type of the expression appropriately.

Lean allows users to mark such subterms as inaccessible for pattern matching.

These annotations are essential, for example, when a term occurring in the left-hand
side is neither a variable nor a constructor application, because these are not
suitable targets for pattern matching.

We can view such inaccessible patterns as "don't care" components of the patterns.
You can declare a subterm inaccessible by writing .(t).

If the inaccessible pattern can be inferred, you can also write _.
-/


/-
The following example, we declare an inductive type that defines the property of
"being in the image of f".

You can view an element of the type ImageOf f b as evidence that b is in the image of f,
whereby the constructor imf is used to build such evidence.


--obscuring what the input is originally

We can then define any function f with an "inverse" which takes anything in the image
of f to an element that is mapped to it.

The typing rules forces us to write f a for the first argument, but this term is neither a
variable nor a constructor application, and plays no role in the pattern-matching definition.

To define the function inverse below, we have to mark f a inaccessible.
-/

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a --b:β is .(f a) , and plays no role as imf tells us everything
  --boiler plate will prove b must of of (f a) type

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a


--my version
def inverse'' {f : α → β} {b : β}:ImageOf f b → α
  | imf a => a

--proof my version is equal to the original
example {f : α → β} {b : β} (im: ImageOf f b) : inverse' b im = inverse'' im := by
  cases im
  rfl

/-
In the example above, the inaccessible annotation makes it clear that f is not a
pattern matching variable.

Inaccessible patterns can be used to clarify and control definitions that make use of
dependent pattern matching.

Consider the following definition of the function Vector.add, which adds two vectors
of elements of a type, assuming that type has an associated addition function:
-/

namespace Hidden

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs) --structural recursion



/-
The argument {n : Nat} appear after the colon, because it cannot be held fixed throughout the definition.

When implementing this definition, the equation compiler starts with a case distinction
as to whether the first argument is 0 or of the form n+1.

This is followed by nested case splits on the next two arguments, and in each case the equation compiler rules
out the cases are not compatible with the first pattern.

But, in fact, a case split is not required on the first argument; the
casesOn eliminator for Vector automatically abstracts this argument and replaces it by 0 and n + 1 when
we do a case split on the second argument.

Using inaccessible patterns, we can prompt the equation compiler to avoid the case split on n
-/


def add' [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | .(_), nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)

/-
Marking the position as an inaccessible pattern tells the equation compiler first,
that the form of the argument should be inferred from the constraints posed
by the other arguments, and, second, that the first argument should not participate
in pattern matching.

The inaccessible pattern .(_) can be written as _ for convenience.
-/
def add'' [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | _, nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)

/-
As we mentioned above, the argument {n : Nat} is part of the pattern matching, because
it cannot be held fixed throughout the definition.

In previous Lean versions, users often found it cumbersome to have to include these
extra discriminants.

Thus, Lean 4 implements a new feature, discriminant refinement, which includes these
extra discriminants automatically for us.
-/

def add''' [Add α] {n : Nat} : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)

/-
When combined with the auto bound implicits feature, you can simplify the
declare further and write:
-/

def add'''' [Add α] : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)

def head : Vector α (n+1) → α
  | cons a as => a

def tail : Vector α (n+1) → Vector α n
  | cons a as => as

theorem eta : (v : Vector α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vector α n → Vector β n → Vector (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)


end Vector
end Hidden
