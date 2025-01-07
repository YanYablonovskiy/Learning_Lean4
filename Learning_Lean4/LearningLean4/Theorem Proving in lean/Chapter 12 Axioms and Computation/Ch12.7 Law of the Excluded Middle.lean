/-
The Law of the Excluded Middle:

The law of the excluded middle is the following
-/

open Classical

#check (@em : ∀ (p : Prop), p ∨ ¬p)


/-
Diaconescu's theorem states that the axiom of choice is sufficient to derive
the law of excluded middle.

More precisely, it shows that the law of the excluded middle follows from Classical.choice,
propext, and funext.

We sketch the proof that is found in the standard library.

First, we import the necessary axioms, and define two predicates U and V:
-/

open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩


/-
If p is true, then every element of Prop is in both U and V. If p is false, then U is the singleton true, and V is the singleton false.

Next, we use some to choose an element from each of U and V:
-/
  let u : Prop := choose exU
  let v : Prop := choose exV

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV

/-
Each of U and V is a disjunction, so u_def and v_def represent four cases.

In one of these cases, u = True and v = False, and in all the other cases, p is true.

Thus we have:
-/

   have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
/-
On the other hand, if p is true, then, by function extensionality and propositional
extensionality, U and V are equal.

By the definition of u and v, this implies that they are equal as well.
-/

    have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _

/-
Putting these last two facts together yields the desired conclusion:
-/

    match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h

/-
Consequences of excluded middle include double-negation elimination, proof by cases,
and proof by contradiction, all of which are described in the Section Classical Logic.

The law of the excluded middle and propositional extensionality imply
propositional completeness:
-/

open Classical
  theorem propComplete (a : Prop) : a = True ∨ a = False :=
    match Classical.em a with
    | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
    | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))

/-
Together with choice, we also get the stronger principle that every proposition is
decidable.

Recall that the class of Decidable propositions is defined as follows:
-/

class inductive Decidable' (p : Prop) where
  | isFalse (h : ¬p) : Decidable' p
  | isTrue  (h : p)  : Decidable' p

/-
In contrast to p ∨ ¬ p, which can only eliminate to Prop, the type Decidable p is
equivalent to the sum type Sum p (¬ p), which can eliminate to any type.

It is this data that is needed to write an if-then-else expression.
-/

/-
As an example of classical reasoning, we use choose to show that if f : α → β is injective
and α is inhabited, then f has a left inverse.

To define the left inverse linv, we use a dependent if-then-else expression.

Recall that if h : c then t else e is notation for dite c (fun h : c => t) (fun h : ¬ c => e).

In the definition of linv, choice is used twice: first, to show that
(∃ a : A, f a = b) is "decidable," and then to choose an a such that f a = b.

Notice that propDecidable is a scoped instance and is activated by the
open Classical command.

We use this instance to justify the if-then-else expression.

(See also the discussion in Section Decidable Propositions).
-/



noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a)
      _ = choose ex := sorry --dif_pos ex (gives error)
      _ = a         := inj feq

#check dif_pos

/-
From a classical point of view, linv is a function.

From a constructive point of view, it is unacceptable; because there is no way
to implement such a function in general, the construction is not informative.

-/
