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





/-
But what value should we return in the nil case?

Something funny is going on: if v has type Vector α (succ n), it can't be nil,
but it is not clear how to tell that to casesOn.

One solution is to define an auxiliary function:
-/

def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v --v is the vector; motive is a vector not of length zero to its tail
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl






end Hidden
