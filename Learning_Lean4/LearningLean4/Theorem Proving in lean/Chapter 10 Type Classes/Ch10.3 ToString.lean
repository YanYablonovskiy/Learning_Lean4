/-
ToString:

The polymorphic method toString has type {α : Type u} → [ToString α] → α → String.

You implement the instance for your own types and use chaining to convert complex values
into strings.

Lean comes with ToString instances for most builtin types.
-/

#check ToString
#print ToString

structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")
