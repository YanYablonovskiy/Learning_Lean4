-- Lean also allows you to introduce "local" definitions using the let keyword.
-- The expression let a := t1; t2 is definitionally equal to the result of replacing
-- every occurrence of a in t2 by t1.

#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16

-- Here, twice_double x is definitionally equal to the term (x + x) * (x + x).

def square_triple(x : Nat) : Nat :=
  let y := x + x + x; y * y

#eval square_triple 2   -- 36

--You can combine multiple assignments by chaining let statements:
#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64


--The ; can be omitted when a line break is used.


def t (x : Nat) : Nat :=
  let y := x + x
  y * y

  -- Notice that the meaning of the expression let a := t1; t2 is very similar to the meaning of
  -- (fun a => t2) t1, but the two are not the same.

  -- In the first expression, you should think of every instance of a in t2 as a syntactic abbreviation for t1.

  -- In the second expression, a is a variable, and the expression fun a => t2 has to make sense independently of the value of a.

  -- The let construct is a stronger means of abbreviation, and there are expressions of the form let a := t1; t2 that cannot be expressed as
  -- (fun a => t2) t1.

  --As an exercise, try to understand why the definition of foo below type checks,
  -- but the definition of bar does not.

  def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
 -- The type of def bar is illdefined, it is a dependent arrow from space of a -> (a -> Nat), applied to
 -- any type?
