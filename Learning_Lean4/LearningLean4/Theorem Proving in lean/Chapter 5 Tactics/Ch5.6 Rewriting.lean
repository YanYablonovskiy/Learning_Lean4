/-
The rewrite tactic (abbreviated rw) and the simp tactic were introduced briefly in Calculational Proofs.

In this section and the next, we discuss them in greater detail.
-/
section
variable (q p:Prop)

example (h:q = p): q = p := by
rw [h] --only works on equality


example (h:p = q): q = p := by
rw [h] --only works on equality
end

#check Eq.comm

/-
The rewrite tactic provides a basic mechanism for applying substitutions to goals and hypotheses,
providing a convenient and efficient way of working with equality.

The most basic form of the tactic is rewrite [t], where t is a term whose type asserts an equality.

For example, t can be a hypothesis h : x = y in the context; it can be a general lemma,
like add_comm : ∀ x y, x + y = y + x, in which the rewrite tactic tries
to find suitable instantiations of x and y;
or it can be any compound term asserting a concrete or general equation.

In the following example, we use this basic form to rewrite the goal using a hypothesis.
-/

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0 --using congrArg
  rw [h₁] -- replace f 0 with 0


--my version, no tactics
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
 have s₁:f k = f 0 := (congrArg f h₂)
 have s₂:f k = 0 := Eq.trans s₁ h₁
 s₂

/-
In the example above, the first use of rw replaces k with 0 in the goal f k = 0.

Then, the second one replaces f 0 with 0.

The tactic automatically closes any goal of the form t = t.

Here is an example of rewriting using a compound expression:
-/


variable (x y : Nat) (p : Nat → Prop) (q : Prop)

example  (h : q → x = y)(h' : p y) (hq : q) : p x := by
  --rewrite takes h hq which is x=y (and y=x) to get goal as p y, and closes it via assumption h'
  rw [h hq]; assumption

/-
Here, h hq establishes the equation x = y.
-/

/-
Multiple rewrites can be combined using the notation rw [t_1, ..., t_n], which is
just shorthand for rw [t_1]; ...; rw [t_n].

The previous example can be written as follows:
-/
