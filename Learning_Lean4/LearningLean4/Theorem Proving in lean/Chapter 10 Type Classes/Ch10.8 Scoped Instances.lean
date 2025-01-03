/-
Scoped Instances:

You can also declare scoped instances in namespaces.

This kind of instance is only active when you are inside of the namespace or open
the namespace.
-/

structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- instance `Add Point` is not active anymore

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

/-
You can use the command open scoped <namespace> to activate scoped attributes but will not "open"
the names from the namespace.
-/



namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }



end Point

open scoped Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'
