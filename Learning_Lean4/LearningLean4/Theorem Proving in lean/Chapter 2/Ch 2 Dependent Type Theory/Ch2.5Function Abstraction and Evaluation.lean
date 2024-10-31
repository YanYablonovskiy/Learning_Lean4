#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred

def funk: Nat -> Nat := fun (x: Nat) ↦ x
#eval funk 5

#eval (λ x : Nat => x + 5) 10    -- 15

-- Creating a function from another expression is a process known as lambda abstraction.
--  Suppose you have the variable x : α and you can construct an expression t : β,
--  then the expression fun (x : α) => t, or, equivalently, λ (x : α) => t, is an object of type α → β.
--  Think of this as the function from α to β which maps any value x to the value t.

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

-- Lean interprets the final three examples as the same expression; in the last expression,
--  Lean infers the type of x and y from the expression if not y then x + 1 else x + 2.

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool

#check fun x : Int => x


-- Think about what these expressions mean. The expression fun x : Nat => x denotes the identity function on Nat,
--  the expression fun x : Nat => true denotes the constant function that always returns true, and fun
--  x : Nat => g (f x) denotes the composition of f and g.
--  You can, in general, leave off the type annotation and let Lean infer it for you. So, for example,
--  you can write fun x => g (f x) instead of fun x : Nat => g (f x).
--_
-- What is the difference between def and fun? Essentially none, it is like a lambda absraction. Same is true for
-- 'proofs' of theorems.
--_
-- You can pass functions as parameters and by giving them names f and g you can then use those functions
--  in the implementation:
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)

-- (String → Bool) → (Nat → String) → Nat → Bool

-- You can also pass types as parameters:


#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

-- The last expression, for example, denotes the function that takes three types, α, β, and γ,
-- and two functions, g : β → γ and f : α → β, and returns the composition of g and f.

-- (Making sense of the type of this function requires an understanding of dependent products,
-- which will be explained below.)



-- The general form of a lambda expression is fun x : α => t, where the variable x is a "bound variable":
-- it is really a placeholder, whose "scope" does not extend beyond the expression t.
--  For example, the variable b in the expression fun (b : β) (x : α) => b has nothing to do with the constant b declared earlier.
--   In fact, the expression denotes the same function as fun (u : β) (z : α) => u.

-- Formally, expressions that are the same up to a renaming of bound variables are called alpha equivalent,
-- and are considered "the same." Lean recognizes this equivalence.

-- Related to the univalence? and curry howard isomorphism?

-- Notice that applying a term t : α → β to a term s : α yields an expression t s : β.
-- Returning to the previous example and renaming bound variables for clarity,
-- notice the types of the following expressions:

#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f1 (n : Nat) : String := toString n
def g1 (s : String) : Bool := s.length > 0

#check (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g1 f1 0
  -- Bool
