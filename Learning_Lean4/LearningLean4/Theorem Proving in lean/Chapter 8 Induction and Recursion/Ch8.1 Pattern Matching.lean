/-
Induction and Recursion:

In the previous chapter, we saw that inductive definitions provide a powerful means of introducing new types in Lean.

Moreover, the constructors and the recursors provide the only means of defining functions on these types.

By the propositions-as-types correspondence, this means that induction is the fundamental method of proof.

Lean provides natural ways of defining recursive functions, performing pattern matching,
and writing inductive proofs.

It allows you to define a function by specifying equations that it should satisfy, and
it allows you to prove a theorem by specifying how to handle various cases that can arise.

Behind the scenes, these descriptions are "compiled" down to primitive recursors, using
a procedure that we refer to as the "equation compiler."

The equation compiler is not part of the trusted code base; its output consists of terms that are
checked independently by the kernel.
-/

/-
Pattern Matching:

The interpretation of schematic patterns is the first step of the compilation process.

We have seen that the casesOn recursor can be used to define functions and prove theorems by cases,
according to the constructors involved in an inductively defined type.

But complicated definitions may use several nested casesOn applications, and may be hard to read and understand.

Pattern matching provides an approach that is more convenient, and familiar to
users of functional programming languages.

Consider the inductively defined type of natural numbers.

Every natural number is either zero or succ x, and so you can define a function from the natural
numbers to an arbitrary type by specifying a value in each of those cases:
-/
open Nat

def sub1 : Nat → Nat --no := anymore
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false

/-
The equations used to define these functions hold definitionally:
-/
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl

/-
Instead of zero and succ, we can use more familiar notation:
-/
def subone : Nat → Nat
  | 0   => 0
  | x+1 => x

def isZero' : Nat → Bool
  | 0   => true
  | x+1 => false

/-
Because addition and the zero notation have been assigned the [match_pattern] attribute,
they can be used in pattern matching.

Lean simply normalizes these expressions until the constructors zero and succ are exposed.

Pattern matching works with any inductive type, such as products and option types:
-/
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0

/-
Here we use it not only to define a function, but also to carry out a proof by cases:
-/

namespace Hidden

def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  --like match on the existential
  | true  => rfl  -- proof that not (not true) = true
  | false => rfl  -- proof that not (not false) = false

/-
Pattern matching can also be used to destruct inductively defined propositions:
-/
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁ --because p ∧ q can only be of one constructor

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp --taking care of both constructors
  | Or.inr hq => Or.inl hq


/-
This provides a compact way of unpacking hypotheses that make use of logical connectives.

In all these examples, pattern matching was used to carry out a single case distinction.

More interestingly, patterns can involve nested constructors, as in the following examples.
-/

def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x

/-
The equation compiler first splits on cases as to whether the input is zero or of the form succ x.

--if succ x, checks whether its succ zero (1)

It then does a case split on whether x is of the form zero or succ x'.

It determines the necessary case splits from the patterns that are presented to it, and raises an error
if the patterns fail to exhaust the cases.

Once again, we can use arithmetic notation, as in the version below.

In either case, the defining equations hold definitionally.
-/

example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl

/-
You can write #print sub2 to see how the function was compiled to recursors.

(Lean will tell you that sub2 has been defined in terms of an internal auxiliary function,
sub2.match_1, but you can print that out too.)

Lean uses these auxiliary functions to compile match expressions.

Actually, the definition above is expanded to
-/

#print sub2

def sub2Full : Nat → Nat :=
  fun x =>
    match x with
    | 0   => 0
    | 1   => 0
    | x+2 => x

/-
Here are some more examples of nested pattern matching:
-/
example (p q : α → Prop)
        : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2

/-
The equation compiler can process multiple arguments sequentially.

For example, it would be more natural to define the previous example as a function of two arguments:
-/

def foo1 : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2

/-
Here is another example:
-/
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a  --constructor with a as argument; a :: as
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b

--function that returns the sum of the heads of two lists
-- defined as 0 if the list is empty

/-
Note that the patterns are separated by commas.

In each of the following examples, splitting occurs on only the first argument, even though the others are included among the list of patterns.
-/
