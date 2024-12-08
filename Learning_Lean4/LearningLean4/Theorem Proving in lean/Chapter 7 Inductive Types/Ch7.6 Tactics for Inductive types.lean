/-
Tactics for Inductive Types:

Given the fundamental importance of inductive types in Lean, it should not be surprising that there are a
number of tactics designed to work with them effectively. We describe some of them here.

The cases tactic works on elements of an inductively defined type, and does what the name suggests:
it decomposes the element according to each of the possible constructors.

In its most basic form, it is applied to an element x in the local context.

It then reduces the goal to cases in which x is replaced by each of the constructions.

-/
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : Nat ⊢ p (succ a)

/-
There are extra bells and whistles.

For one thing, cases allows you to choose the names for each alternative using a with clause.

In the next example, for example, we choose the name m for the argument to succ, so that the
second case refers to succ m.

More importantly, the cases tactic will detect any items in the local context that depend on the target variable.

It reverts these elements, does the split, and reintroduces them.

In the example below, notice that the hypothesis h : n ≠ 0 becomes h : 0 ≠ 0 in the first branch,
and h : succ m ≠ 0 in the second.
-/
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero => --changes the h to be the right case of n
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl

/-
Notice that cases can be used to produce data as well as prove propositions.
-/
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

--mine, using  match:
def f_1 (n : Nat) : Nat :=
 match n with
 | zero => 3
 | succ n => 7

---predecessor or 3
def f_2 (n : Nat) : Nat :=
 match n with
 | zero => 3
 | succ n => n

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

example : f_1 0 = 3 := rfl
example : f_1 5 = 7 := rfl

example : f_2 0 = 3 := rfl
example : f_2 5 = 4 := rfl



/-
Once again, cases will revert, split, and then reintroduce dependencies in the context.
-/


def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }


--if tuple is length 0, then 3, otherwise 7
def ft {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩ --how you create { . // .} pairs

example : ft myTuple = 7 :=
  rfl

-- my version
def myTuple_1: Tuple Nat 3 :=
Subtype.mk [0,1,2] rfl

/-
Here is an example of multiple constructors with arguments.
-/
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b --is either of form bar1 a b or bar2
  | bar2 c d e => exact e

--my stuff
def silly_1 (x: Foo) : Bool := by
cases x with
| bar1 a b => cases a
              case bar1.zero => exact true
              case bar1.succ n => exact false
| bar2 c d e => exact false

def myFoo: Foo :=
Foo.bar2 3 3 3


def myFoo1: Foo :=
Foo.bar1 0 3

#eval silly_1 myFoo
#eval silly_1 myFoo1

/-
The alternatives for each constructor don't need to be solved in the
order the constructors were declared.
-/
def silly' (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b

/-
The syntax of the with is convenient for writing structured proofs.

Lean also provides a complementary case tactic, which allows you to focus
on goal assign variable names.
-/
def silly'' (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b --same order
  case bar2 c d e => exact e

/-
The case tactic is clever, in that it will match the constructor to the appropriate goal.

For example, we can fill the goals above in the opposite order:
-/
def silly''' (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b

/-
You can also use cases with an arbitrary expression.

Assuming that expression occurs in the goal, the cases tactic will generalize over the expression,
introduce the resulting universally quantified variable, and case on that.
-/
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k --generalises result ∀ n p n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)

/-
Think of this as saying "split on cases as to whether m + 3 * k is zero
or the successor of some number."

The result is functionally equivalent to the following:
-/

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n --changes to p n from p (m + 3 * k)
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a) ; dont need induction since have hs

/-
Notice that the expression m + 3 * k is erased by generalize; all that matters is whether it is of the form 0 or succ a.

This form of cases will not revert any hypotheses that also mention the expression in the equation
(in this case, m + 3 * k).

If such a term appears in a hypothesis and you want to generalize over that as well,
you need to revert it explicitly.

If the expression you case on does not appear in the goal,
the cases tactic uses have to put the type of the expression into the context.

Here is an example:
-/

example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n --creates a have m < n ∨ m ≥ n using Nat.lt_or_ge
  case inl hlt => exact h₁ hlt --have less than; case m < n
  case inr hge => exact h₂ hge --have greater than; case m ≥ n


/-
The theorem Nat.lt_or_ge m n says m < n ∨ m ≥ n, and it is natural to think of the proof
above as splitting on these two cases.

In the first branch, we have the hypothesis hlt : m < n, and in the second
we have the hypothesis hge : m ≥ n.

The proof above is functionally equivalent to the following:
-/

example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

/-
After the first two lines, we have h : m < n ∨ m ≥ n as a hypothesis, and we simply do cases on that.

Here is another example, where we use the decidability of equality on the
natural numbers to split on the cases m = n and m ≠ n.
-/
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  --rewrite using heq; get n - n = 0 ∨ n ≠ n as goal
  --use Nat.sub_self n to get goal in the left of or
  | inr hne => apply Or.inr; exact hne
  --can get the result directly; Or.inr on m ≠ n

--using Classical
example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Classical.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  --rewrite using heq; get n - n = 0 ∨ n ≠ n as goal
  --use Nat.sub_self n to get goal in the left of or
  | inr hne => apply Or.inr; exact hne
  --can get the result directly; Or.inr on m ≠ n

  --difference between Classical.em vs Decidable.em?

  #check Decidable

/-
Remember that if you open Classical, you can use the law of the excluded
middle for any proposition at all.

But using type class inference (see Chapter Type Classes),
Lean can actually find the relevant decision procedure,
which means that you can use the case split in a computable function.
-/

/-
Just as the cases tactic can be used to carry out proof by cases, the induction tactic can be used
to carry out proofs by induction.

The syntax is similar to that of cases, except that the argument can only be a term in the local context.

Here is an example:
-/
theorem zero_add_short (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

/-
As with cases, we can use the case tactic instead of with.
-/
theorem zero_add_long (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]

/-
Here are some additional examples:
-/

open Nat
#check Nat.add_zero


theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp only [*, Nat.add_zero, add_succ]
  --Nat.add_zero takes care of the zero case
  --Nat.add_succ makes succ m + succ n into succ (m + succ n)
  --then ih turns it into succ ( succ (m + n))

--longer version
example (m n: Nat):  succ m + n = succ (m + n) := by
induction n
case zero => simp [*]
case succ n ih => simp only [add_succ,ih]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp  only [*, Nat.add_zero, add_succ, Nat.succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp only [*, Nat.add_zero, add_succ]

/-
The induction tactic also supports user-defined induction principles
with multiple targets (aka major premises).
-/
/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption

--base case after the induction; order can be swapped


example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁ --absurd from y > 0 and ¬ y > 0
    | Or.inr h₁ => --case for ¬ y ≤ x
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h

  /-
  You can use the match notation in tactics too:
  -/
  example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2

  /-
  As a convenience, pattern-matching has been integrated into tactics such as intro and funext.
  -/
  example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  --first arg is of form ⟨_, ⟨hq, _⟩⟩ and second argument is of form ⟨hp, _⟩
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩ --using And.intro

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

  /-
  We close this section with one last tactic that is designed to facilitate working with inductive types, namely,
  the injection tactic.

  By design, the elements of an inductive type are freely generated, which is to say,
  the constructors are injective and have disjoint ranges.

  The injection tactic is designed to make use of this fact:
  -/



example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h' --goes back one step; injection meaning using inverse
  injection h' with h'' --goes back one more step
  rw [h''] --rewrites using m=n

/-
The first instance of the tactic adds h' : succ m = succ n to the context,
and the second adds h'' : m = n.

The injection tactic also detects contradictions that arise when different constructors are
set equal to one another, and uses them to close the goal.
-/
open Nat

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction

/-
As the second example shows,
the contradiction tactic also detects contradictions of this form.
-/
