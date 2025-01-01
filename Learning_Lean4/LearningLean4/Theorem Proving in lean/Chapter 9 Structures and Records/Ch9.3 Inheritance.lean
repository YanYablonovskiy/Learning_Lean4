/-
Inheritance:

We can extend existing structures by adding new fields.

This feature allows us to simulate a form of inheritance.
-/
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color


/-
In the next example, we define a structure using multiple inheritance,
and then define an object using objects of the parent structures.
-/

structure Point' (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point' α, RGBValue where
  no_blue : blue = 0

def p : Point' Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl } --no blue is a prop term that needs construction

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
