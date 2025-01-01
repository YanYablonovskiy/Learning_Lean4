/-
Objects

We have been using constructors to create elements of a structure type.

For structures containing many fields, this is often inconvenient, because we have to
remember the order in which the fields were defined.

Lean therefore provides the following alternative notations for defining elements
of a structure type.
-/

/-
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
-/

/-
The suffix : structure-type can be omitted whenever the name of the
structure can be inferred from the expected type.

For example, we use this notation to define "points."

The order that the fields are specified does not matter,
so all the expressions below define the same point.
-/
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr


inductive Point' (α: Type u) where
 | mk: α → α → Point' α
--wont work with the bottom notation

inductive Point'' (α: Type u) where
 | mk: (x:α) → (y:α) → Point'' α




#check { x := 10, y := 20 : Point Nat }  -- Point ℕ
#check { y := 20, x := 10 : Point _ }
#check ({ x := 10, y := 20 } : Point Nat)

example : Point Nat :=
  { y := 20, x := 10 }

/-
If the value of a field is not specified, Lean tries to infer it.

If the unspecified fields cannot be inferred, Lean flags an error indicating
the corresponding placeholder could not be synthesized.
-/

structure MyStruct where
    {α : Type u} --named, but implicit
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct } --α implicitly found as Nat and
                                         --β impilictly as Bool

/-
Record update is another common operation which amounts to creating a new record object by modifying
the value of one or more fields in an old one.

Lean allows you to specify that unassigned fields in the specification of a record should be taken
from a previously defined structure object s by adding the annotation s with before the field assignments.

If more than one record object is provided, then they are visited in order until Lean finds one that contains the unspecified field.

Lean raises an error if any of the field names remain unspecified after all the objects are visited.
-/



def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
