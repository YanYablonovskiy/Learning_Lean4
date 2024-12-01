/-
Tactic combinators are operations that form new tactics from old ones.

A sequencing combinator is already implicit in the by block:
-/
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption

/-

Here, apply Or.inl; assumption is functionally equivalent to a single tactic
which first applies apply Or.inl and then applies assumption.

In t₁ <;> t₂, the <;> operator provides a parallel version of the sequencing operation:
t₁ is applied to the current goal, and then t₂ is applied to all the resulting subgoals:

-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption --using constructor for And, and using assumptions

--my version, using normal sequencer

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
 apply And.intro; assumption; assumption

/-
This is especially useful when the resulting goals can be finished off in a uniform way, or,
at least, when it is possible to make progress on all of them uniformly.

The first | t₁ | t₂ | ... | tₙ applies each tᵢ until one succeeds, or else fails:
-/

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

--works as a proof of 'having one of hp or hq'

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

/-
In the first example, the left branch succeeds, whereas in the second one, it is the right one that succeeds.

In the next three examples, the same compound tactic succeeds in each case:
-/
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  --first branch works if you have p, and doesnt repeat
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  --second branch works on q making q ∨ r, then repeat gives p ∨ q ∨ r
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  --same as with q
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

/-
The tactic tries to solve the left disjunct immediately by assumption; if that fails,
it tries to focus on the right disjunct; and if that doesn't work, it invokes
the assumption tactic.
-/

/-
You will have no doubt noticed by now that tactics can fail.

Indeed, it is the "failure" state that causes the first combinator to backtrack and
try the next tactic.

The try combinator builds a tactic that always succeeds, though possibly in a trivial way:
try t executes t and reports success, even if t fails.

It is equivalent to first | t | skip, where skip is a tactic that does nothing
(and succeeds in doing so).

In the next example, the second constructor succeeds on the right conjunct q ∧ r
(remember that disjunction and conjunction associate to the right) but fails on the first.

The try tactic ensures that the sequential composition succeeds:
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

--without 'try' gives the error 'tactic 'constructor' failed, target is not an inductive datatype'
--because after constructor, this is And.intro, and have goals left as p and q ∧ r.
--So running constructor on all goals fails when trying it on p

--my version
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  repeat (first|constructor|assumption)

  /-
  Be careful: repeat (try t) will loop forever, because the inner tactic never fails.
  -/

  /-
  In a proof, there are often multiple goals outstanding.

  Parallel sequencing is one way to arrange it so that a single tactic is applied to multiple goals,
  but there are other ways to do this.

  For example, all_goals t applies t to all open goals:
  -/

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

  --my version
  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  apply And.intro hp <;> repeat (constructor <;> assumption)

  /-
  In this case, the any_goals tactic provides a more robust solution.

  It is similar to all_goals, except it succeeds if its argument succeeds on
  at least one goal:
  -/
  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

  --my version

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  repeat (any_goals (first|constructor|assumption))

  /-
  The first tactic in the by block below repeatedly splits conjunctions:
  -/
  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

/-
In fact, we can compress the full tactic down to one line:
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
/-
The combinator focus t ensures that t only effects the current goal, temporarily
hiding the others from the scope.

So, if t ordinarily only effects the current goal, focus (all_goals t)
has the same effect as t.
-/
