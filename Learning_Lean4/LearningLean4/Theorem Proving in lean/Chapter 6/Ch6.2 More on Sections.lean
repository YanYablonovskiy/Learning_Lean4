/-
Lean provides various sectioning mechanisms to help structure a theory. 

You saw in Variables and Sections that the section command makes it possible 
not only to group together elements of a theory that go together, 
but also to declare variables that are inserted as arguments to theorems and definitions, 
as necessary. 

Remember that the point of the variable command is to declare 
variables for use in theorems, as in the following example:
-/

section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end

/-
The definition of double does not have to declare x as an argument; Lean detects the dependence 
and inserts it automatically. 

Similarly, Lean detects the occurrence of x in t1 and t2, and inserts it automatically there, too. 

Note that double does not have y as argument. 

Variables are only included in declarations where they are actually used.
-/
