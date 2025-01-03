/-
Chaining Instances
If that were the extent of type class inference, it would not be all that impressive; it would be
simply a mechanism of storing a list of instances for the elaborator to find in a lookup table.

What makes type class inference powerful is that one can chain instances.

That is, an instance declaration can in turn depend on an implicit instance of a type class. This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

For example, the following definition shows that if two types a and b are inhabited,
then so is their product:
-/

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

/-
With this added to the earlier instance declarations, type class instance can infer,
for example, a default element of Nat × Bool:
-/

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)

/-
Similarly, we can inhabit type function with suitable constant functions:
-/

instance [Inhabited b] : Inhabited (a → b) where
  default := fun _ => default

/-
As an exercise, try defining default instances for other types, such as List and Sum types.
-/


namespace ex

instance [Inhabited b]: Inhabited (List b) where
default := List.cons default List.nil

instance [Inhabited b] [Inhabited a]: Inhabited (Sum a b) where
default := Sum.inl default



end ex

/-
The Lean standard library contains the definition inferInstance.

It has type {α : Sort u} → [i : α] → α, and is useful for triggering the type class resolution
procedure when the expected type is an instance.

-/

#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl


/-
You can use the command #print to inspect how simple inferInstance is.
-/

#print inferInstance

/-
@[reducible] def inferInstance.{u} : {α : Sort u} → [i : α] → α :=
fun {α} [i : α] ↦ i
-/
