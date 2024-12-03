/-
In Lean, the type of natural numbers, Nat, is different from the type of integers, Int.

But there is a function Int.ofNat that embeds the natural numbers in the integers,
meaning that we can view any natural number as an integer, when needed.

Lean has mechanisms to detect and insert coercions of this sort.
-/

variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
