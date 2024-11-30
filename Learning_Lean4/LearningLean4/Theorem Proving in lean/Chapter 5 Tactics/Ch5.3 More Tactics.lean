/-
Some additional tactics are useful for constructing and destructing propositions and data.

For example, when applied to a goal of the form p ∨ q, you use
tactics such as apply Or.inl and apply Or.inr.

Conversely, the cases tactic can be used to decompose a disjunction:
-/
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h -- introducing h: p ∨ q
  cases h with -- casing the disjunction, with either p or q
  | inl hp => apply Or.inr; exact hp --swapping hence inl to inr
  | inr hq => apply Or.inl; exact hq

/-
Note that the syntax is similar to the one used in match expressions.

The new subgoals can be solved in any order:
-/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq --swapping the order compared to the prior example
  | inl hp => apply Or.inr; exact hp

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq --swapping the order compared to the prior example
  | inl hp => apply Or.inr; exact hp



/-
You can also use a (unstructured) cases without the with and a
tactic for each alternative:
-/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

--unstructured, so just put tactics until they solve a goal then moving on to next

/-
The (unstructured) cases is particularly useful when you can close
several subgoals using the same tactic:
-/

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h --both goals are the same, and so are the hypothesis, so repeat works
  repeat assumption

/-
You can also use the combinator tac1 <;> tac2 to apply tac2 to each subgoal
produced by tactic tac1:
-/
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption --like repeat assumption

/-
You can combine the unstructured cases tactic with the case and . notation:
-/
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h --making case inl and inr; inl meaning needing the right (p)
  . apply Or.inr --entering case inl; applying Or.inr needs p
    assumption --already have p via the case
  . apply Or.inl
    assumption

--


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h --introducing the hypothesis p ∨ q
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

--the addition of h doesnt seem to change anything? annotating which case its coming from?
-- can do something when _ cant synthesise, in this case implicit worked

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h --introducing the hypothesis p ∨ q
  cases h
  case inr =>
    apply Or.inl
    assumption
  case inl =>
    apply Or.inr
    assumption

--mixing explicit case notation, and implicit

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption

  /-
  The cases tactic can also be used to decompose a conjunction:
  -/
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with --can only have the one case, since conjunction, it is the case with all conjuncts inhabited
  | intro hp hq => constructor; exact hq; exact hp --constructor is like apply And.intro


  example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with --can only have the one case, since conjunction, it is the case with all conjuncts inhabited
  | intro hp hq => apply And.intro ; exact hq; exact hp --version with apply, instead of constructor.
  --constructor implictly finds a introduction rule to apply, and an introduction rule invokes the constructor

  /-
  In this example, there is only one goal after the cases tactic is applied, with
  h : p ∧ q replaced by a pair of assumptions, hp : p and hq : q.

  The constructor tactic applies the unique constructor for conjunction, And.intro.


  With these tactics, an example from the previous section can be rewritten as follows:
  -/


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro --two cases mp and mpr
  --entering mpr: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
  . intro h --introducting h:p ∧ (q ∨ r) ; inhabitant of p ∧ (q ∨ r) inductive type.
    cases h with --cases on conjunction eliminator; just one elimination rule
    | intro hp hqr =>
      cases hqr --two cases for elimination of (q ∨ r)
      . apply Or.inl; constructor <;> assumption --case hq; applying Or.inl meaning we need goal p ∧ q
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro --two cases mp and mpr
  --entering mpr: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
  . intro h --introducting h:p ∧ (q ∨ r) ; inhabitant of p ∧ (q ∨ r) inductive type.
    cases h with --cases on conjunction eliminator; just one elimination rule
    | intro hp hqr =>
      cases hqr --two cases for elimination of (q ∨ r)
      . apply Or.inl; apply And.intro <;> assumption --hq:q , applying Or.inl leaves with p ∧ q
      . apply Or.inr; apply And.intro <;> assumption --hp:p , applying Or.inr leaves with p ∧ r
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr

/-
You will see in Chapter Inductive Types that these tactics are quite general.

The cases tactic can be used to decompose any element of an inductively defined type;
constructor always applies the first applicable constructor of an inductively defined type.

For example, you can use cases and constructor with an existential quantifier:
-/
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h --introducing (∃x, p x)
  cases h with --case of inductively defined existence type; if for all x px implies p x ∨ q x
  | intro x px => constructor; apply Or.inl; exact px --constructor uses apply Exists.intro

--my versions,

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h --introducing (∃x, p x)
  cases h with --case of inductively defined existence type; if for all x px implies p x ∨ q x
  | intro x px => apply Exists.intro; apply Or.inl; apply px

/-
Here, the constructor tactic leaves the first component of the existential assertion, the value of x, implicit.

It is represented by a metavariable, which should be instantiated later on.

In the previous example, the proper value of the metavariable is determined by the tactic exact px,
since px has type p x.

If you want to specify a witness to the existential quantifier explicitly, you can use the exists tactic instead:
-/

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

-- my version

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  apply Exists.elim h
  intro a hpa
  apply Exists.intro a --keeping constructor explicit
  apply Or.inl
  apply hpa

/-
Here is another example:
-/
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h --introducing h:(∃ x, p x ∧ q x)
  cases h with --introducing cases; case is for all x:Nat , goal  p x ∧ q x → ∃ x, q x ∧ p x
  | intro x hpq =>
    cases hpq with --entering cases for And, which has one case having both p and q
    | intro hp hq =>
      exists x --applying exists intro

/-
These tactics can be used on data just as well as propositions.

In the next example, they are used to define functions which swap the components of the product and sum types:
-/
def swap_pair : α × β → β × α := by --conjunction
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by  --disjunction
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

--my versions

def swap_pair_tctless : α × β → β × α :=  --conjunction
  fun (h:α × β) => (h.2,h.1)

def swap_pair_tctless₁ (h: α × β):β × α := (h.2,h.1)

#print swap_pair_tctless
#print swap_pair_tctless₁

def swap_sum_tctless: Sum α β → Sum β α :=
 fun (h:Sum α β) => if x:(h.getLeft?.isSome = true) then
   Sum.inr (h.getLeft?.get (x)) else
   if y:(h.getRight?.isSome = true) then
    Sum.inl (h.getRight?.get (y))
   else
   sorry

/-
Note that up to the names we have chosen for the variables, the definitions are identical to the proofs
of the analogous propositions for conjunction and disjunction.

The cases tactic will also do a case distinction on a natural number:
-/
--example of cases for an inductive type

section
open Nat

example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'

--my example

example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by --proof of P by induction
  revert m
  intro k
  cases k with
  | zero    => exact h₀
  | succ k' => exact h₁ k'
end

/-
The cases tactic, and its companion, the induction tactic, are discussed in
greater detail in the Tactics for Inductive Types section.

The contradiction tactic searches for a contradiction among the hypotheses of the current goal:
-/
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h --intro p ∧ ¬p ;
  cases h --cases for p ∧ ¬p ; hp ,hnp
  contradiction --contrdiction using hnp hp.elim

--my versions

example (p q : Prop) : p ∧ ¬ p → q :=
fun h:_ => (h.2 h.1).elim

/-
You can also use match in tactic blocks.
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h --intoducing h:p ∧ (q ∨ r)
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr

/-
You can "combine" intro h with match h ... and write the previous examples as follows
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption
