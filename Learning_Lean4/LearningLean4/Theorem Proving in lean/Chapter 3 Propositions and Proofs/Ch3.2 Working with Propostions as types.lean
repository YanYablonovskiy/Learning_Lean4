variable {p : Prop}
variable {q : Prop}

#check p → q → p
#check p ∧ q
#check p → q
#check p ∧ q = p → q
#check p ∧ q → p = p → q → p



#check  And q p = And q p
#check  Iff q p =  p → q → p

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
theorem t1b (a: Prop) (b: Prop):  a → b → a := fun ha : a => fun hb : b => ha --arguments explicit
-- For lean, an inhabitant of type p is a proof of p. A proof of p implies q , using arrows is p → q.
-- As arrows associate from the right, this is really p → (q → p); and (q → p) is true for any q if p is always true.

-- For example, the following is not true in general:
-- theorem t1_f : (p → q) → p := fun hp : p => fun hq : q => hp
-- In Lean, q → p is saying if a true fact q then true fact p, rather than any q implying p.
/-

Compare this proof to the expression fun x : α => fun y : β => x of type α → β → α, where α and β are data types.
This describes the function that takes arguments x and y of type α and β, respectively, and returns x.
The proof of t1 has the same form, the only difference being that p and q are elements of Prop rather than Type.

Intuitively, our proof of p → q → p assumes p and q are true, and uses the first hypothesis (trivially) to establish
that the conclusion, p, is true.

Note that the theorem command is really a version of the def command:
under the propositions and types correspondence, proving the theorem p → q → p is really the same as defining an element of the associated type.
To the kernel type checker, there is no difference between the two.

-/
#check fun hp : p => fun hq : q => hp
def t2 : p → q → p := fun hp : p => fun hq : q => hp
-- This seems similar to some sort of recursion.
def α := p → q
def β := q → p
#check t2
#check t1
#check t1b
#check @t1 α β
#check t1b α β
#check α
/-
There are a few pragmatic differences between definitions and theorems, however.

In normal circumstances, it is never necessary to unfold the "definition" of a theorem;
by proof irrelevance, any two proofs of that theorem are definitionally equal.
Once the proof of a theorem is complete, typically we only need to know that the proof exists;
it doesn't matter what the proof is.

In light of that fact, Lean tags proofs as irreducible,
which serves as a hint to the parser (more precisely, the elaborator) that there
is generally no need to unfold them when processing a file.

In fact, Lean is generally able to process and check proofs in parallel,
since assessing the correctness of one proof does not require knowing the details of another.

As with definitions, the #print command will show you the proof of a theorem:

-/
--Irreducible here just means Lean doesn't try to check its actual equality to anything, since all that
--matters for the proof to exist is the types, and all that matters is that at least one exists for the statement
--to be true.

/-
Notice that the lambda abstractions hp : p and hq : q can be viewed as temporary assumptions in the proof of t1.
Lean also allows us to specify the type of the final term hp, explicitly, with a show statement:
-/
theorem t1_show : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

  -- Linter highlights hq as unused, which makes sense.
  -- The previous version simply returned hp, and lean knew it was p from the definition of hp.
  -- Here it is stated explicitly, representing the users expectations and throwing an exception.

/-
Adding such extra information can improve the clarity of a proof and help detect errors when writing a proof.
The show command does nothing more than annotate the type, and, internally, all the presentations of t1
that we have seen produce the same term.

As with ordinary definitions, we can move the lambda-abstracted variables to the left of the colon:

-/

theorem t1_short (hp : p) (hq : q) : p := hp

def adding (n: Nat) (m: Nat): Nat := m+ n
def adding_2 (p : Nat × Nat): Nat := p.1 + p.2

#check adding
#check adding_2


#print t1_short    -- p → q → p
#print t1_show
#print t1

-- In the previous version, t1 returns a composition taking p to hq, and hq taking q to hp,
-- Before the terminal arrow, given a p then this takes us to a q → p; waiting for a q.
-- p is witnessed by hp, which in turns is provided as input(given); if its variable this way then
-- this is equivalent to a forall

/-
We can use the theorem t1 just as a function application:
-/



axiom hp : p

theorem t3 : q → p := t1 hp -- the theorem is p → (q → p)
theorem t4 : q → p := t1_short hp

/-
The axiom declaration postulates the existence of an element of the given type and may compromise logical consistency.
For example, we can use it to postulate that the empty type False has an element:
-/

axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound


/-
Declaring an "axiom" hp : p is tantamount to declaring that p is true, as witnessed by hp.
Applying the theorem t1 : p → q → p to the fact hp : p that p is true yields the theorem t1 hp : q → p.

Recall that we can also write theorem t1 as follows:

-/

theorem t6 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
#print t6


/-
The type of t1 is ∀ {p q : Prop}, p → q → p.
We can read this as the assertion "for every pair of propositions p q, we have p → q → p."

For example, we can move all parameters to the right of the colon:
-/

--Here p → (q → p), and if you construct p → .. this means p is true.
--(q → p) would then mean, q is true and it implies p is true. Since p is always true, any true
--statement will imply it.

theorem t1_long : ∀ {p q : Prop}, p → q → p := --∀ helps readability?
  fun {p q : Prop} (hp : p) (hq : q) => hp
/-
If p and q have been declared as variables, Lean will generalize them for us automatically:
-/

section

variable {p q : Prop}

theorem t1_dual_var : p → q → p := fun (hp : p) (hq : q) => hp


end
/-
In fact, by the propositions-as-types correspondence, we can declare the assumption hp that p holds,
 as another variable:
-/
section
variable {p q : Prop}
variable (hp : p)

theorem t1_very_short : q → p := fun (hq : q) => hp
end

/-
Lean detects that the proof uses hp and automatically adds hp : p as a premise.
In all cases, the command #print t1 still yields ∀ p q : Prop, p → q → p.

Remember that this type can just as well be written ∀ (p q : Prop) (hp : p) (hq : q), p,
since the arrow denotes nothing more than an arrow type in which the target does not depend on the bound variable.
-/
-- otherwise it would be (a: p) → pa

variable (p q r s : Prop)

#check t1b p q                -- p → q → p
#check t1b r s                -- r → s → r
#check t1b (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1b (r → s) (s → r) h  -- (s → r) → r → s
-- this is because t1b (r → s) (s → r)    -- (r → s) → (s → r) → r → s
-- and applied to h is then (s → r) → r → s

/-
As another example, let us consider the composition function discussed in the last chapter,
now with propositions instead of types.
-/

theorem t₁ (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

  /-
  As a theorem of propositional logic, what does t2 say?

Note that it is often useful to use numeric unicode subscripts, entered as \0, \1, \2, ...,
for hypotheses, as we did in this example.
  -/


-- t₂ (q → r) → ((p → q) → (p → r)) -- transitivity
-- proof by applying h₁ to ( h₂ h₃) : (h₂ h₃) → r
-- and h₂ h₃ is h₃ → p .. so then we have p → r ?
