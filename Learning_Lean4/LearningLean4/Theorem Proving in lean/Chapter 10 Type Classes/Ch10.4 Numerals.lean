/-
Numerals
Numerals are polymorphic in Lean.

You can use a numeral (e.g., 2) to denote an element of any type that implements
the type class OfNat. --has an instance of that type
-/

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat

#check (2: Int)

/-
Lean elaborates the terms (2 : Nat) and (2 : Rational) as OfNat.ofNat Nat 2 (instOfNatNat 2)
and OfNat.ofNat Rational 2 (instOfNatRational 2) respectively.

We say the numerals 2 occurring in the elaborated terms are raw natural numbers.

You can input the raw natural number 2 using the macro nat_lit 2.
-/
#check nat_lit 2  -- Nat

/-
Raw natural numbers are not polymorphic.

The OfNat instance is parametric on the numeral.

So, you can define instances for particular numerals.

The second argument is often a variable as in the example above,
or a raw natural number.
-/

class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
