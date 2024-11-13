/-
The expression Or.intro_left q hp creates a proof of p ∨ q from a proof hp : p.

Similarly, Or.intro_right p hq creates a proof for p ∨ q using a proof hq : q.

These are the left and right or-introduction rules.


-/

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

#check Or.intro_left
#check Or.intro_right
#print Or.intro_left

#check Or.inl --shorter version with the other (not proven) prop inferred as a implicit arg
#print Or.inl

#check Or.inr
#print Or.inr

/-

The or-elimination rule is slightly more complicated.
The idea is that we can prove r from p ∨ q, by showing that r follows from p and that r follows from q.
In other words, it is a proof by cases.

In the expression Or.elim hpq hpr hqr, Or.elim takes three arguments, hpq : p ∨ q, hpr : p → r and hqr : q → r,
and produces a proof of r.

In the following example, we use Or.elim to prove p ∨ q → q ∨ p.

-/
#check Or.elim
#print Or.elim

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h --the first argument and hypothesis
    (fun hp : p => -- p → q ∨ p , the second argument
      show q ∨ p from Or.intro_right q hp) -- use p and right introduction for or to get q ∨ p
    (fun hq : q => -- q → q ∨ p , the third argument
      show q ∨ p from Or.intro_left p hq)  -- use q and left introduction for or to get q ∨ p

/-
In most cases, the first argument of Or.intro_right and Or.intro_left can be inferred automatically by Lean.

Lean therefore provides Or.inr and Or.inl which can be viewed as shorthand for Or.intro_right _ and Or.intro_left _.

Thus the proof term above could be written more concisely:
-/
-- my ver
example (h : p ∨ q) : q ∨ p :=
  Or.elim h --the first argument and hypothesis
    (fun hp : p => show q ∨ p from Or.inr hp) --inferring the other argument as q, producing  p → q ∨ p , the second argument
    (fun hq : q => -- q → q ∨ p , the third argument
      Or.inl hq)  -- use q and left introduction for or to get q ∨ p


--From TPIL version

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq) -- all in one line, using or elim to show q ∨ p follows from p and from q
                                                        -- and we have p ∨ q hence the conclusion  q ∨ p follows

/-
Notice that there is enough information in the full expression for Lean to infer the types of hp and hq as well.

But using the type annotations in the longer version makes the proof more readable, and can help catch and debug errors.

Because Or has two constructors, we cannot use anonymous constructor notation.
But we can still write h.elim instead of Or.elim h:
-/

-- Essentially, can't use ⟨ ⟩ to have many or statements like ⟨ h.intro_left , h.intro_right ..
-- as its not an inductive type with one constructor

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

/-
Once again, you should exercise judgment as to whether such abbreviations enhance or diminish readability.
-/
