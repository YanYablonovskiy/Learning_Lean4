/-
Enumerated types are a very special case of inductive types, in which the constructors take no arguments at all.

In general, a "construction" can depend on data, which is then represented in the constructed argument.

Consider the definitions of the product type and sum type in the library:
-/
namespace Hidden

inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
/-
Consider what is going on in these examples.

The product type has one constructor, Prod.mk, which takes two arguments.

To define a function on Prod α β, we can assume the input is of the form Prod.mk a b,
and we have to specify the output, in terms of a and b.

We can use this to define the two projections for Prod.

Remember that the standard library defines notation α × β for Prod α β and (a, b)
for Prod.mk a b.
-/
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b

def A := Prod.mk 1 2

#check fst A


--my version
def fstTactic {α : Type u} {β : Type v} (p : Prod α β) : α := by
  cases p
  . case mk ha hb => exact ha

/-
The function fst takes a pair, p. The match interprets p as a pair, Prod.mk a b.

Recall also from Dependent Type Theory that to give these definitions
the greatest generality possible, we allow the types α and β to belong to any universe.

Here is another example where we use the recursor Prod.casesOn instead of match.
-/

--hidden version
def prod_example (p : Prod Bool Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

end Hidden

--non-hidden version
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

/-
The argument motive is used to specify the type of the object you want to construct,
and it is a function because it may depend on the pair.

The cond function is a boolean conditional: cond b t1 t2 returns t1 if b is true,
and t2 otherwise.

The function prod_example takes a pair consisting of a boolean, b, and a number, n,
and returns either 2 * n or 2 * n + 1 according to whether b is true or false.
-/

/-
In contrast, the sum type has two constructors, inl and inr (for "insert left" and "insert right"),
each of which takes one (explicit) argument.

To define a function on Sum α β, we have to handle two cases:
either the input is of the form inl a, in which case we have to specify an output value in terms of a,
or the input is of the form inr b, in which case we have to specify an output value in terms of b.
-/
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

--my version with match:
def sum_example_match (s: Sum Nat Nat): Nat :=
match s with
| Sum.inr a => 2*a
| Sum.inl b => 2*b + 1

--with tactics:
def sum_example_tactics (s: Sum Nat Nat): Nat := by
cases s
. case inl a => exact 2*a
. case inr b => exact (2*b + 1)


#eval sum_example (Sum.inl 3)
#eval sum_example_tactics (Sum.inr 3)

#check @sum_example
#check Prod
#check @Prod

/-
This example is similar to the previous one, but now an input to sum_example is implicitly either of the form inl n or inr n.

In the first case, the function returns 2 * n, and the second case, it returns 2 * n + 1.

Notice that the product type depends on parameters α β : Type which are arguments
to the constructors as well as Prod.

Lean detects when these arguments can be inferred from later arguments to a constructor or the return type,
and makes them implicit in that case.
-/

/-
In Section Defining the Natural Numbers we will see what happens when the constructor of an inductive type
takes arguments from the inductive type itself.

What characterizes the examples we consider in this section is that each constructor
relies only on previously specified types.

Notice that a type with multiple constructors is disjunctive:
an element of Sum α β is either of the form inl a or of the form inl b.

A constructor with multiple arguments introduces conjunctive information:
from an element Prod.mk a b of Prod α β we can extract a and b.

An arbitrary inductive type can include both features,
by having any number of constructors, each of which takes any number of arguments.

As with function definitions, Lean's inductive definition syntax will let you put
named arguments to the constructors before the colon:
-/

namespace Hidden1

inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β -- as opposed to | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β

--as opposed to
--  | inl : α → Sum α β
--  | inr : β → Sum α β


end Hidden1

/-
The results of these definitions are essentially the same as the ones given earlier in this section.

A type, like Prod, that has only one constructor is purely conjunctive:
the constructor simply packs the list of arguments into a single piece of data,
essentially a tuple where the type of subsequent arguments can depend on the type of the initial argument.

We can also think of such a type as a "record" or a "structure".

In Lean, the keyword structure can be used to define such an inductive type as well
as its projections, at the same time.
-/
namespace Hidden2

structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)

end Hidden2

/-
This example simultaneously introduces the inductive type, Prod, its constructor, mk,
the usual eliminators (rec and recOn), as well as the projections, fst and snd,
as defined above.

If you do not name the constructor, Lean uses mk as a default.

For example, the following defines a record to store a color as a triple of RGB values:
-/
structure Color where
  (red : Nat) (green : Nat) (blue : Nat) --just defining projections; mk implicit
  deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow --255

/-
The definition of yellow forms the record with the three values shown,
and the projection Color.red returns the red component.

You can avoid the parentheses if you add a line break between each field.
-/
structure ColorShort where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr

/-
The structure command is especially useful for defining algebraic structures, and Lean provides substantial infrastructure to support working with them.

Here, for example, is the definition of a semigroup:
-/
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

--mine
structure UnitalSemigroup where
  carrier : Type u
  unit: carrier
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  unital: ∀a, (mul a unit = a) ∧ (mul unit a = a)

/-
We will see more examples in Chapter Structures and Records.

We have already discussed the dependent product type Sigma:
-/
namespace Hidden

inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β -- makes each pair ⟨a, β a⟩

/-
Two more examples of inductive types in the library are the following:
-/
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α


/-
In the semantics of dependent type theory, there is no built-in notion of a partial function.

Every element of a function type α → β or a dependent function type (a : α) → β is assumed to have a value at every input.

The Option type provides a way of representing partial functions.

An element of Option β is either none or of the form some b, for some value b : β.

Thus we can think of an element f of the type α → Option β as being a partial function from α to β:
for every a : α, f a either returns none, indicating f a is "undefined", or some b.
-/

/-
An element of Inhabited α is simply a witness to the fact that there is an element of α.

Later, we will see that Inhabited is an example of a type class in Lean:
Lean can be instructed that suitable base types are inhabited, and can automatically
infer that other constructed types are inhabited on that basis.
-/

/-
As exercises, we encourage you to develop a notion of composition for partial functions from α to β and β to γ,
and show that it behaves as expected.

We also encourage you to show that Bool and Nat are inhabited, that the product of two inhabited types
is inhabited, and that the type of functions to an inhabited type is inhabited.
-/
