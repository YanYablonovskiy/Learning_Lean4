/-
Finally, consider the existential quantifier, which can be written as either exists x : α, p x or ∃ x : α, p x.

Both versions are actually notationally convenient abbreviations for a more long-winded expression,

Exists (fun x : α => p x), defined in Lean's library.
-/

#check Exists
#print axioms Exists
#print axioms Exists.intro

/-
As you should by now expect, the library includes both an introduction rule and an elimination rule.

The introduction rule is straightforward: to prove ∃ x : α, p x, it suffices to provide a suitable
term t and a proof of p t.

Here are some examples:
-/

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0 -- showing 1 is such a Nat, and using exists
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h -- 0 < x by h, hence such an example is introduced

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p

--my version

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  have  p:(x < y) ∧ (y < z):= And.intro hxy hyz
  Exists.intro y p

/-
We can use the anonymous constructor notation ⟨t, h⟩ for Exists.intro t h,
when the type is clear from the context.
-/
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

--my version
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  have  p:(x < y) ∧ (y < z):= And.intro hxy hyz
  ⟨y,p⟩

/-
Note that Exists.intro has implicit arguments: Lean has to infer the predicate p : α → Prop in the conclusion ∃ x, p x.

This is not a trivial affair. For example, if we have hg : g 0 0 = 0 and write Exists.intro 0 hg,
there are many possible values for the predicate p, corresponding
to the theorems ∃ x, g x x = x, ∃ x, g x x = 0, ∃ x, g x 0 = x, etc.

Lean uses the context to infer which one is appropriate.
This is illustrated in the following example, in which we set the option pp.explicit
to true to ask Lean's pretty-printer to show the implicit arguments.
-/
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 (hg : g 0 0 = 0): ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0): ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0): ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0): ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

/-
We can view Exists.intro as an information-hiding operation, since it hides the witness to
the body of the assertion.

The existential elimination rule, Exists.elim, performs the opposite operation.

It allows us to prove a proposition q from ∃ x : α, p x, by showing that q follows from p w
for an arbitrary value w.

Roughly speaking, since we know there is an x satisfying p x, we can give it a name, say, w.

If q does not mention w, then showing that q follows from p w is tantamount to showing that
q follows from the existence of any such x.

Here is an example:
-/

-- if ∀ w: α , p w → q; then ∃ x : α, p x → q

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with -- kind of like a big or statement, and match works for checking constructors
  | ⟨(w : α), hw⟩ => ⟨w, hw.right, hw.left⟩

-- my version
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
 Exists.elim (h) (fun (w:α) => (fun (hw: p w ∧ q w) => Exists.intro w (And.intro hw.2 hw.1)))

--(q w ∧ p w: (And.intro ((h w).2) ((h w).1))))

#check Exists.elim

/-
The match expression is part of Lean's function definition system, which provides convenient and expressive ways of defining complex functions.

Once again, it is the Curry-Howard isomorphism that allows us to co-opt this mechanism for writing proofs as well.

The match statement "destructs" the existential assertion into the components w and hw,
which can then be used in the body of the statement to prove the proposition.

We can annotate the types used in the match for greater clarity:

-/

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with --h destructs into w and hw, otherwise will be named by default
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, ⟨ hw.right, hw.left ⟩ ⟩

/-
We can even use the match statement to decompose the conjunction at the same tim
-/
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
/-
Lean also provides a pattern-matching let expression:
-/
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

/-
This is essentially just alternative notation for the match construct above.
Lean will even allow us to use an implicit match in the fun expression:
-/

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
/-
We will see in Chapter Induction and Recursion that all these variations are instances
of a more general pattern-matching construct.

In the following example, we define is_even a as ∃ b, a = 2 * b, and then we show
that the sum of two even numbers is an even number.
-/
def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 ( fun w1 (hw1 : a = 2 * w1) => --using exists elim to get w1 out of h1, so for arbitrary w1, hw1 implies
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>  --using exists elim to get w2 out of h2, so for abritrary w1, hw1 implies for arbitrary w2 hw2 implies
    Exists.intro (w1 + w2)                      -- in other words, for arbitrary w1, w2, h1w1 h2w2 implies is_even w1 + w2
      (calc a + b --w1 + w2 example of such an element, for arbitrary w1 + w2 satisfying h1 h2
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2] --using the universal assumptions on arbitrary w1 w2
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add]))) --rewriting to obtain proof (w1 + w2) is suitable

/-
Using the various gadgets described in this chapter --- the match statement, anonymous constructors,
and the rewrite tactic, we can write this proof concisely as follows:

-/
theorem even_plus_even_1 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩ --using anon exists construction


/-
Just as the constructive "or" is stronger than the classical "or," so, too, is the constructive "exists" stronger than the classical "exists".

For example, the following implication requires classical reasoning because,
from a constructive standpoint, knowing that it is not the case that every x
satisfies ¬ p is not the same as having a particular x that satisfies p.
-/
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
