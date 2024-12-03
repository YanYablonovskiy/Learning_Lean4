/-
The split tactic is useful for breaking nested if-then-else and match expressions in cases.

For a match expression with n cases, the split tactic generates at most n subgoals.

Here is an example:
-/
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction --the case when x=5, contradiction
  . contradiction --the case when y=5, contradiction
  . contradiction --the case when z=5, contradiction
  . rfl --the case when none are equal to 5; so its equal to 1

  /-
  We can compress the tactic proof above as follows.
  -/
  example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl

  /-
  The tactic split <;> first | contradiction | rfl first applies the split tactic,
  and then for each generated goal it tries contradiction, and then rfl if contradiction fails.

  Like simp, we can apply split to a particular hypothesis:
  -/
def g (xs ys : List Nat) : Nat :=
match xs, ys with
| [a, b], _ => a+b+1
| _, [b, c] => b+1
| _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp_arith at h
