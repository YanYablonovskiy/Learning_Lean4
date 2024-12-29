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







/-
But what value should we return in the nil case?

Something funny is going on: if v has type Vector α (succ n), it can't be nil,
but it is not clear how to tell that to casesOn.

One solution is to define an auxiliary function:
-/

def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn
    (motive := fun x _ => x = n + 1 → Vector α n) -- → {motive : (a : Nat) → Vector α a → Sort v} →
     --here x is the length of the vector; _ is the vector; Sort is the type of x = n + 1 → Vector α n
     v --v is the vector; motive is a vector not of length zero to its tail
    (fun h : 0 = n + 1 => Nat.noConfusion h) -- → motive 0 nil, produces a term of any type if 0 = n + 1
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) => --
       Nat.noConfusion h --motive (n + 1)?
       (fun h1 : m = n => h1 ▸ as)) --(cons a as)

def tail_long (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl

/-
In the nil case, m is instantiated to 0, and noConfusion makes use of the fact that
0 = succ n cannot occur.

Otherwise, v is of the form a :: w, and we can simply return w, after casting it
from a vector of length m to a vector of length n.
-/

/-

The difficulty in defining tail is to maintain the relationships between the indices.

The hypothesis e : m = n + 1 in tailAux is used to communicate the relationship
between n and the index associated with the minor premise.

Moreover, the zero = n + 1 case is unreachable, and the canonical way to
discard such a case is to use noConfusion.
-/

/-
The tail function is, however, easy to define using recursive equations,
and the equation compiler generates all the boilerplate code automatically for us.

Here are a number of similar examples:
-/
def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs) --structural recursion

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs) --list of lists

/-
The map function is even more tedious to define by hand than the tail function.

We encourage you to try it, using recOn, casesOn and noConfusion.
-/


end Vector


end Hidden
