/-
Decidable Propositions:

Let us consider another example of a type class defined in the standard library, namely the type class of Decidable propositions.

Roughly speaking, an element of Prop is said to be decidable if we can decide whether it is true or false.

The distinction is only useful in constructive mathematics; classically, every proposition is decidable.

But if we use the classical principle, say, to define a function by cases, that function will not be computable.

Algorithmically speaking, the Decidable type class can be used to infer a procedure that effectively determines whether or not the proposition is true.

As a result, the type class supports such computational definitions when they are possible while at the same time allowing a smooth transition
to the use of classical definitions and classical reasoning.

In the standard library, Decidable is defined formally as follows:
-/
namespace ex


class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p

--we have evidence for either ¬p or p

/-
Logically speaking, having an element t : Decidable p is stronger than having an element t : p ∨ ¬p; it enables us to define values
of an arbitrary type depending on the truth value of p.

--because to eliminate p ∨ ¬p you must provide a case for both; but to eliminate Decidable you dont?

For example, for the expression if p then a else b to make sense, we need to know that p is decidable.

That expression is syntactic sugar for ite p a b, where ite is defined as follows:
-/


def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t) --if not true, e (else); otherwise if true t (then)

-- only depends on truth value not on c itself


/-
The standard library also contains a variant of ite called dite, the dependent if-then-else expression.

It is defined as follows:
-/
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t --if true then t (c), else e (c)

-- depends both on truth value and the type of c


/-
That is, in dite c t e, we can assume hc : c in the "then" branch, and hnc : ¬ c in the "else" branch.

To make dite more convenient to use, Lean allows us to write if h : c then t else e instead of dite c (λ h : c => t) (λ h : ¬ c => e).
-/

/-
Without classical logic, we cannot prove that every proposition is decidable.

But we can prove that certain propositions are decidable.

For example, we can prove the decidability of basic operations like equality and comparisons on the natural numbers and the integers.

Moreover, decidability is preserved under propositional connectives:
-/

#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot

/-
Thus we can carry out definitions by cases on decidable predicates on the natural numbers:
-/

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step

/-
Turning on implicit arguments shows that the elaborator has inferred the decidability of the proposition x < a ∨ x > b,
simply by applying appropriate instances.

With the classical axioms, we can prove that every proposition is decidable.

You can import the classical axioms and make the generic instance of decidability
available by opening the Classical namespace.
-/
end ex


namespace Classical

noncomputable scoped
instance (priority := low) propDecidable' (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

/-
This guarantees that Lean will favor other instances and fall back on propDecidable only
after other attempts to infer decidability have failed.

The Decidable type class also provides a bit of small-scale automation
for proving theorems.

The standard library introduces the tactic decide that uses the Decidable
instance to solve simple goals.
-/

example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool

/-
They work as follows.

The expression decide p tries to infer a decision procedure for p,
and, if it is successful, evaluates to either true or false.

In particular, if p is a true closed expression, decide p will reduce definitionally to the Boolean true.

On the assumption that decide p = true holds, of_decide_eq_true produces a proof of p.

The tactic decide puts it all together to prove a target p.

By the previous observations, decide will succeed any time the inferred decision procedure for
c has enough information to evaluate, definitionally, to the isTrue case.
-/
