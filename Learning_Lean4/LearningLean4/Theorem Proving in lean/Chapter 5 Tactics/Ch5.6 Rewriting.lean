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

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

  /-
  By default, rw uses an equation in the forward direction, matching the left-hand side
  with an expression(in the goal), and replacing it with the right-hand side.

  The notation ←t can be used to instruct the tactic to use the equality
  t in the reverse direction.
  -/
  example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]


  --my version, tactic less
   example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 :=
    have h:(f a = f b) := congrArg f h₁
    show f b = 0 from Eq.trans (Eq.comm.mp h) h₂

/-
In this example, the term ←h₁ instructs the rewriter to replace b with a. 

In the editors, you can type the backwards arrow as \l. 

You can also use the ascii equivalent, <-.

Sometimes the left-hand side of an identity can match more than one subterm in the pattern, 
in which case the rw tactic chooses the first match it finds when traversing the term. 

If that is not the one you want, you can use additional arguments to 
specify the appropriate subterm.
-/
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [
    Nat.add_assoc, --add brackets around b + c
    Nat.add_comm b, --same as b _, rearrange to get a + (c + b)
    ← Nat.add_assoc --rewrite use associativity a + c + b
   ]
--different order 
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, --rewrite as a + (b + c)
     Nat.add_assoc,  --looking for first term to rewrite, finds and does a + (c+b)
     Nat.add_comm b] --rewrites a + (b + c) as a + (c + b)

--another way, changing the left side instead
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc,  --rewrite as a + (b + c)
  Nat.add_assoc,      --looking for first term to rewrite, finds and does a + (c+b)
  Nat.add_comm _ b]   --re-writes a + (c + b) as a + (b + c);appllies refl

/-
In the first example above, the first step rewrites a + b + c to a + (b + c). 

The next step applies commutativity to the term b + c; without specifying the argument, 
the tactic would instead rewrite a + (b + c) to (b + c) + a. 

Finally, the last step applies associativity in the reverse direction, 
rewriting a + (c + b) to a + c + b. 

The next two examples instead apply associativity to move the parenthesis 
to the right on both sides, and then switch b and c. 

Notice that the last example specifies that the rewrite should take 
place on the right-hand side by specifying the second argument to Nat.add_comm.

By default, the rewrite tactic affects only the goal. 

The notation rw [t] at h applies the rewrite t at hypothesis h.
-/
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]


--my version; tacticless
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := 
 have h:a = 0 := Eq.trans (Eq.symm (Nat.add_zero a)) h
 show f a = f 0 from congrArg f h

 /-
The first step, rw [Nat.add_zero] at h, rewrites the hypothesis a + 0 = 0 to a = 0. 

Then the new hypothesis a = 0 is used to rewrite the goal to f 0 = f 0.

The rewrite tactic is not restricted to propositions. 

In the following example, we use rw [h] at t to rewrite the hypothesis 
t : Tuple α n to t : Tuple α 0.
 -/

 def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
