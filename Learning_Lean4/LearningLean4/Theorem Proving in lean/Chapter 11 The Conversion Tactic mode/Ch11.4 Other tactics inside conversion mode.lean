/-
Other tactics inside conversion mode
arg i enter the i-th nondependent explicit argument of an application.
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    arg 2
    -- ⊢ b * c
    rw [Nat.mul_comm]

/-
args alternative name for congr.

simp applies the simplifier to the current goal.

It supports the same options available in regular tactic mode.
-/
def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (h₁ : g x = x + 1) (h₂ : x > 0) : g x = f x := by
  conv =>
    rhs -- f x
    simp [f, h₂] -- apply f
  exact h₁

/-
⬝ <enter [1, x, 2, y]> iterate arg and intro with the given arguments. It is just the macro:

syntax enterArg := ident |> group("@"? num)
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:num]) => `(conv| arg $i)
  | `(conv| enter [@$i:num]) => `(conv| arg @$i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg:enterArg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))

⬝ <done> fail if there are unsolved goals.

⬝ <trace_state> display the current tactic state.

⬝ <whnf> put term in weak head normal form.

⬝ tactic => <tactic sequence> go back to regular tactic mode.
This is useful for discharging goals not supported by conv mode,
and applying custom congruence and extensionality lemmas.


-/

example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    -- ⊢ g x x + x
    arg 1
    -- ⊢ g x x
    rw [h₁]
    -- 2 goals: ⊢ 1, ⊢ x ≠ 0
    . skip
    . tactic => exact h₂

/-

⬝ apply <term> is syntax sugar for tactic => apply <term>.

-/
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂
