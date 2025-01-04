/-
Pattern matching:

Navigation using the above commands can be tedious.

One can shortcut it using pattern matching as follows:
-/


example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]

/-
which is just syntax sugar for
-/
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]

/-
Of course, wildcards are allowed:
-/
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
