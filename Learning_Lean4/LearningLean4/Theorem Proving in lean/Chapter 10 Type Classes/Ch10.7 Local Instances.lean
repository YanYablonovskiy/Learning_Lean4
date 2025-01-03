/-
Local Instances

Type classes are implemented using attributes in Lean.

Thus, you can use the local modifier to indicate that they only have effect until
the current section or namespace is closed, or until the end of the current file.
-/

structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- instance `Add Point` is not active anymore

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance

/-
You can also temporarily disable an instance using the attribute command until the
current section or namespace is closed, or until the end of the current file.
-/

structure Point' where
  x : Nat
  y : Nat

instance addPoint : Add Point' where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double' (p : Point') :=
  p + p

attribute [-instance] addPoint

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance

/-
We recommend you only use this command to diagnose problems.
-/
