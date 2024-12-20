/-
Dependent Pattern Matching:

All the examples of pattern matching we considered in Section Pattern Matching can easily be written
using casesOn and recOn.

However, this is often not the case with indexed inductive families such as Vector α n,
since case splits impose constraints on the values of the indices.

Without the equation compiler, we would need a lot of boilerplate code to define very simple functions
such as map, zip, and unzip using recursors.

To understand the difficulty, consider what it would take to define a function tail which takes a
vector v : Vector α (succ n) and deletes the first element.

A first thought might be to use the casesOn function:
-/

namespace Hidden



inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check @Vector.casesOn
/-
  {α : Type u}
  → {motive : (a : Nat) → Vector α a → Sort v} →
  → {a : Nat} → (t : Vector α a)
  → motive 0 nil
  → ((a : α) → {n : Nat} → (a_1 : Vector α n) → motive (n + 1) (cons a a_1))
  → motive a t
-/

end Vector



end Hidden
