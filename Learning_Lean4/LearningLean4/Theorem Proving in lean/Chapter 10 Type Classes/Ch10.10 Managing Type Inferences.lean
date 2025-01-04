/-
Managing Type Class Inference:

If you are ever in a situation where you need to supply an expression
that Lean can infer by type class inference, you can ask Lean to carry
out the inference using inferInstance:
-/

def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
-- {α : Sort u} → [α] → α

#check foo.add 5
/-
In fact, you can use Lean's (t : T) notation to specify the class whose
instance you are looking for, in a concise manner:
-/

#check (inferInstance : Add Nat)

/-
You can also use the auxiliary definition inferInstanceAs:
-/

#check inferInstanceAs (Add Nat)

#check @inferInstanceAs
-- (α : Sort u) → [α] → α

/-
Sometimes Lean can't find an instance because the class is buried under
a definition.

For example, Lean cannot find an instance of Inhabited (Set α).

We can declare one explicitly:
-/

def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance
 @[reducible]
 def Set' (a: Type u) := a → Prop

--works
example : Inhabited (Set' α) :=
 inferInstance


instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

/-
At times, you may find that the type class inference fails to find an
expected instance, or, worse, falls into an infinite loop and times out.

To help debug in these situations, Lean enables you to request a trace
of the search:
-/
set_option trace.Meta.synthInstance true

/-
If you are using VS Code, you can read the results by hovering over
the relevant theorem or definition, or opening the messages window
with Ctrl-Shift-Enter.

In Emacs, you can use C-c C-x to run an independent Lean process on
your file, and the output buffer will show a trace every time the
type class resolution procedure is subsequently triggered.

You can also limit the search using the following options:
-/


set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400


/-
Option synthInstance.maxHeartbeats specifies the maximum amount of 
heartbeats per typeclass resolution problem. 

A heartbeat is the number of (small) memory allocations (in thousands), 
0 means there is no limit. 

Option synthInstance.maxSize is the maximum number of instances used to 
construct a solution in the type class instance synthesis procedure.

Remember also that in both the VS Code and Emacs editor modes, tab 
completion works in set_option, to help you find suitable options.

As noted above, the type class instances in a given context represent 
a Prolog-like program, which gives rise to a backtracking search. 

Both the efficiency of the program and the solutions that are found 
can depend on the order in which the system tries the instance. 

Instances which are declared last are tried first. 

Moreover, if instances are declared in other modules, the order in 
which they are tried depends on the order in which namespaces are opened. 

Instances declared in namespaces which are opened later are tried earlier.

You can change the order that type class instances are tried by 
assigning them a priority. 

When an instance is declared, it is assigned a default priority value. 

You can assign other priorities when defining an instance. 

The following example illustrates how this is done:
-/
class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
