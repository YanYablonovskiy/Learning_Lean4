/-
Structuring conversion tactics:

Curly brackets and . can also be used in conv mode to structure tactics:
-/

example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
