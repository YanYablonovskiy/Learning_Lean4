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
