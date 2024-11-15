/-
The introduction and elimination rules we have seen so far are all constructive, which is to say,
they reflect a computational understanding of the logical connectives based on the propositions-as-types correspondence.

Ordinary classical logic adds to this the law of the excluded middle, p ∨ ¬p.
To use this principle, you have to open the classical namespace.
-/
open Classical

variable (q : Prop)
#check em q
#print em



-- **Diaconescu's theorem**: excluded middle from choice, Function extensionality and propositional extensionality. -/
-- theorem Classical.em : ∀ (p : Prop), p ∨ ¬p :=
-- fun p ↦
--   let U := fun x ↦ x = True ∨ p;
--   let V := fun x ↦ x = False ∨ p;
--   let_fun exU := Exists.intro True (Or.inl rfl);
--   let_fun exV := Exists.intro False (Or.inl rfl);
--   let u := choose exU;
--   let v := choose exV;
--   let_fun u_def := choose_spec exU;
--   let_fun v_def := choose_spec exV;
--   let_fun not_uv_or_p :=
--     match u_def, v_def with
--     | Or.inr h, x => Or.inr h
--     | x, Or.inr h => Or.inr h
--     | Or.inl hut, Or.inl hvf =>
--       let_fun hne :=
--         of_eq_true
--           (Eq.trans (congr (congrArg Ne hut) hvf)
--             (Eq.trans (congrArg Not (Eq.trans Init.Core._auxLemma.2 (Eq.trans (iff_false True) not_true_eq_false)))
--               not_false_eq_true));
--       Or.inl hne;
--   let_fun p_implies_uv := fun hp ↦
--     let_fun hpred :=
--       funext fun x ↦
--         let_fun hl := fun x_1 ↦ Or.inr hp;
--         let_fun hr := fun x_1 ↦ Or.inr hp;
--         let_fun this := propext { mp := hl, mpr := hr };
--         this;
--     let_fun h₀ :=
--       Eq.mpr (id (congrArg (fun _a ↦ ∀ (exU : ∃ x, _a x) (exV : ∃ x, V x), choose exU = choose exV) hpred))
--         fun exU exV ↦ Eq.refl (choose exU);
--     let_fun this := h₀ exU exV;
--     this;
--   match not_uv_or_p with
--   | Or.inl hne => Or.inr (mt p_implies_uv hne)
--   | Or.inr h => Or.inl h



/-
Intuitively, the constructive "Or" is very strong: asserting p ∨ q amounts to knowing which is the case.

If RH represents the Riemann hypothesis, a classical mathematician is willing to assert RH ∨ ¬RH,
even though we cannot yet assert either disjunct.

One consequence of the law of the excluded middle is the principle of double-negation elimination:
-/
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p) -- the or statement
    (fun hp : p => hp) -- p is implied by the or
    (fun hnp : ¬p => absurd hnp h) -- p is implied with ¬p in the or combined with ¬¬p and absurd

-- dont need to specify the implicit arguments type:

theorem dne₁ (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

#check @dne
#check dne

#check dne₁
variable (h₃: ¬¬q)
variable (h₄: ¬q)
#check h₃

#check dne h₃
#check Not ¬q

/-
Double-negation elimination allows one to prove any proposition, p, by assuming ¬p and deriving false, because that amounts to proving ¬¬p.

In other words, double-negation elimination allows one to carry out a proof by contradiction, something which
is not generally possible in constructive logic.

As an exercise, you might try proving the converse, that is, showing that em can be proved from dne.
-/
variable (h₂: q ∨ ¬q)
#check @False.elim
#check ¬q
#check fun (h:¬(q ∨ ¬q)) => h


theorem demorg {p q : Prop} (hnem: ¬(p ∨ q)): ¬p ∧ ¬q :=
  have hnp: ¬p := fun (hp: p) => hnem (Or.intro_left q hp)
  have hnq: ¬q := fun (hq: q) => hnem (Or.intro_right p hq)
  show ¬p ∧ ¬q from And.intro hnp hnq

theorem em_from_dne {p: Prop}: p ∨ ¬p :=  --(dne: ¬¬p → p) had this at first, incorrect as its using dne for all prop
have h: ¬(p ∨ ¬p) → ¬p ∧ ¬¬p := fun (h₁:¬(p ∨ ¬p)) => demorg h₁
have h₃:(¬p ∧ ¬¬p) → ¬p ∧ p := fun (h₄:¬p ∧ ¬¬p) => And.intro h₄.1 (dne h₄.2)
have h₅: (¬p ∧ p) → False := fun (h₆:(¬p ∧ p)) => h₆.1 (h₆.2)
have h₇:(¬¬(p ∨ ¬p)):= (fun (h₈:¬(p ∨ ¬p)) => h₅ (h₃ (h h₈)))
show p ∨ ¬p from dne₁ h₇

#check @em_from_dne
#check (∀{q : Prop}, (¬¬q → q))

theorem em_from_dne₁ {p: Prop} (dne: ∀{q : Prop}, (¬¬q → q)): p ∨ ¬p :=
have h: ¬(p ∨ ¬p) → ¬p ∧ ¬¬p := fun (h₁:¬(p ∨ ¬p)) => demorg h₁
have h₃:(¬p ∧ ¬¬p) → ¬p ∧ p := fun (h₄:¬p ∧ ¬¬p) => And.intro h₄.1 (dne h₄.2)
have h₅: (¬p ∧ p) → False := fun (h₆:(¬p ∧ p)) => h₆.1 (h₆.2)
have h₇:(¬¬(p ∨ ¬p)):= (fun (h₈:¬(p ∨ ¬p)) => h₅ (h₃ (h h₈)))
show p ∨ ¬p from dne h₇


#check @em_from_dne₁
/-
The classical axioms also give you access to additional patterns of proof that can be justified by appeal to em.
For example, one can carry out a proof by cases:
-/

example (h : ¬¬p) : p :=
  byCases --automatically uses em: p ∨ ¬p, like or elim
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

#check byCases
/-
Or you can carry out a proof by contradiction:
-/

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p => --using em and or elim
     show False from h h1)
/-
If you are not used to thinking constructively, it may take some time for you to get a sense of where
classical reasoning is used.

It is needed in the following example because, from a constructive standpoint,
knowing that p and q are not both true does not necessarily tell you which one is false:

-/

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)

--my cases version
#check Or.intro_right


example {p q: Prop} (h : ¬(p ∧ q)) : (¬p ∨ ¬q) :=
byCases
  (fun h1:p => (Or.intro_right  (¬p) (show ¬q from fun (hq:q) => h (And.intro h1 hq))))
  (fun h1:¬p => (Or.intro_left  (¬q) h1))

/-
We will see later that there are situations in constructive logic where principles like excluded middle and double-negation elimination are permissible,
and Lean supports the use of classical reasoning in such contexts without relying on excluded middle.

The full list of axioms that are used in Lean to support classical reasoning are discussed in Axioms and Computation.
-/
