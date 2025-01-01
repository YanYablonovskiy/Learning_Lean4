/-
Structures and Records

We have seen that Lean's foundational system includes inductive types.

We have, moreover, noted that it is a remarkable fact that it is possible to construct a substantial edifice of mathematics based on nothing more than the type universes,
dependent arrow types, and inductive types; everything else follows from those.

The Lean standard library contains many instances of inductive types (e.g., Nat, Prod, List), and even the logical connectives are defined using inductive types.

Recall that a non-recursive inductive type that contains only one constructor is called a structure or record.

The product type is a structure, as is the dependent product (Sigma) type. In general, whenever we define a structure S,
we usually define projection functions that allow us to "destruct" each instance of S and retrieve the values that are stored in its fields.

The functions prod.fst and prod.snd, which return the first and second elements of a pair, are examples of such projections.

When writing programs or formalizing mathematics, it is not uncommon to define structures containing many fields.

The structure command, available in Lean, provides infrastructure to support this process. When we define a structure using this command,
Lean automatically generates all the projection functions.

The structure command also allows us to define new structures based on previously defined ones.

Moreover, Lean provides convenient notation for defining instances of a given structure.
-/

/-
Declaring Structures

The structure command is essentially a "front end" for defining inductive data types.

Every structure declaration introduces a namespace with the same name.

The general form is as follows:


    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>

-/

/-
Most parts are optional. Here is an example:
-/

structure Point (α : Type u) where
  mk :: (x : α) (y : α)
  deriving Repr

/-
Values of type Point are created using Point.mk a b, and the fields of a point p are
accessed using Point.x p and Point.y p (but p.x and p.y also work, see below).

The structure command also generates useful recursors and theorems.

Here are some of the constructions generated for the declaration above.
-/

#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection

/-
If the constructor name is not provided, then a constructor is named mk by default.

You can also avoid the parentheses around field names if you add a line break between each field.
-/

structure Point' (α : Type u) where
  x : α
  y : α

/-
Here are some simple theorems and expressions that use the generated constructions.

As usual, you can avoid the prefix Point by using the command open Point.
-/
#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl

/-
Given p : Point Nat, the dot notation p.x is shorthand for Point.x p.

This provides a convenient way of accessing the fields of a structure.
-/
def p' := Point.mk 10 20

#check p'.x  -- Nat
#eval p'.x   -- 10
#eval p'.y   -- 20


/-
The dot notation is convenient not just for accessing the projections of a record, but
also for applying functions defined in a namespace with the same name.

Recall from the Conjunction section if p has type Point, the expression p.foo
is interpreted as Point.foo p, assuming that the first non-implicit argument
to foo has type Point.

The expression p.add q is therefore shorthand for Point.add p q in the example below.
-/

--only works on Point Nat

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- {x := 4, y := 6}
#check p.add _
def l : Point Int := Point.mk 1 2

--#eval p.add l --error

/-
In the next chapter, you will learn how to define a function like add so that it works generically
for elements of Point α rather than just Point Nat, assuming α has an associated addition operation.

More generally, given an expression p.foo x y z where p : Point, Lean will insert p at
the first argument to Point.foo of type Point.

For example, with the definition of scalar multiplication below,
p.smul 3 is interpreted as Point.smul 3 p. (insert as first argument of type point, not just any)
-/

def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p'' : Point Nat := Point.mk 1 2

#eval p''.smul 3  -- {x := 3, y := 6}

#check p.smul _

/-
It is common to use a similar trick with the List.map function, which takes a list as its
second non-implicit argument
-/

#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]

/-
Here xs.map f is interpreted as List.map f xs.
-/
