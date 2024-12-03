/-
Go back to the exercises in Chapter Propositions and Proofs and Chapter Quantifiers and Equality
and redo as many as you can now with tactic proofs, using also rw and simp as appropriate.
-/

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
constructor; repeat (intro h; simp [h])

--v1
example : p ∨ q ↔ q ∨ p := by
constructor;
. intro h
  cases h
  case mp.inl k => apply Or.inr k
  case mp.inr k =>  apply Or.inl k
. intro h
  cases h
  case mpr.inl k => apply Or.inr k
  case mpr.inr k =>  apply Or.inl k
--v2
example : p ∨ q ↔ q ∨ p := by
constructor <;> intro h;
repeat (first|cases h|case _ k => apply Or.inr k|case _ k =>  apply Or.inl k)



-- associativity of ∧ and ∨
--v1
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
constructor;
. intro h
  simp at h
  simp [*]
. intro h
  simp at h
  simp [*]

--v2
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
constructor <;> (intro h; simp at h; simp [*])



example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
rw [← or_assoc]



-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
rw [and_or_left]


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
rw [or_and_left]

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
simp


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
rw [or_imp]

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
rw [not_or]


example : ¬p ∨ ¬q → ¬(p ∧ q) := by
intro h
cases h <;> simp [*]



example : ¬(p ∧ ¬p) := by
 simp

example : p ∧ ¬q → ¬(p → q) := by
simp


example : ¬p → (p → q) := by
intro h
simp [*]


example : (¬p ∨ q) → (p → q) := by
intro h
cases h <;> simp [*]

example : p ∨ False ↔ p := by simp


example : p ∧ False ↔ False := by simp

example : (p → q) → (¬q → ¬p) := by
  intro h
  exact ( (fun nq: ¬q => (fun hp:p => nq (h hp))) )



open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  simp [Decidable.imp_or]



example : ¬(p ∧ q) → ¬p ∨ ¬q := by
intro h
exact (not_and_iff_or_not_not.mp h)


example : ¬(p → q) → p ∧ ¬q := by simp [not_imp]


--v1
example : (p → q) → (¬p ∨ q) := by
intro h
cases em p
case inl hp => apply Or.inr (h hp)
case inr hnp => apply Or.inl hnp


--v2
example : (p → q) → (¬p ∨ q) := by
intro h ; cases em p ;
repeat (first|case inl hp => apply Or.inr (h hp)|case inr hnp => apply Or.inl hnp)


example : (¬q → ¬p) → (p → q) := by
intro h
intro hp
cases em q
case inl hq => exact hq
case inr hnq => exact (False.elim ((h hnq) hp))


example : p ∨ ¬p := em p


example : (((p → q) → p) → p) := by
intro h;
cases em p
case inl hp => exact hp
case inr hnp => exact h ( fun hp:p => by contradiction)

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply forall_and






example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
intro h₁ h₂
simp [*]

--v1
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
intro h
cases h
case inl hpx => simp [*]
case inr hqx => simp [*]


--v2
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
intro h
cases h <;> simp [*]



variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
intro h
constructor
. intro har
  exact har h
. exact ( fun hr:r => fun x:α => hr)


--v1
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . intro mp_Arg
    cases em r
    case mp.inl hr => apply Or.inr hr
    case mp.inr hnr => apply Or.inl
                              (fun (x:α) => (mp_Arg x).elim (fun hpx: p x => hpx)
                              (fun hr:r => False.elim (hnr hr)))
  . intro mpr_arg
    cases mpr_arg
    case mpr.inl hpx => exact (fun (x:α) => Or.inl (hpx x))
    case mpr.inr hr => exact (fun (x:α) => Or.inr hr)







example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
constructor
. intro mp_arg
  exact (fun (hr:r) => fun (x:α) => (mp_arg x) hr)
. intro mpr_arg
  exact ( fun (x:α) => fun (hr:r) => (mpr_arg hr) x)



variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
have shaves_barber_iff_not:shaves barber barber ↔ ¬ shaves barber barber := h barber
simp at shaves_barber_iff_not




example : (∃ x : α, r) → r := by simp

example (a : α) : r → (∃ x : α, r) := by
intro hr
simp [*,Exists.intro a]



example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by simp

--v1
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
constructor
. intro mp_arg
  apply Exists.elim mp_arg
  . exact ( fun (x:α) => fun (hpqx:p x ∨ q x) =>
    (hpqx.elim (fun hpx:p x => Or.inl (Exists.intro x hpx) )
      (fun hqx: q x => Or.inr (Exists.intro x hqx))))
. intro mpr_arg
  cases mpr_arg
  . case mpr.inl hepx => apply Exists.elim hepx; exact ( fun (x:α) => fun hpx:p x => Exists.intro x (Or.inl hpx))
  . case mpr.inr heqx => apply Exists.elim heqx; exact ( fun (x:α) => fun hqx:q x => Exists.intro x (Or.inr hqx))



example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by simp

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by simp

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by simp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by simp

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by simp



variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
constructor
. intro mp_arg
  intro hapx
  cases mp_arg
  . case mp.intro x h =>  exact h (hapx x)
. intro mpr_arg
  cases em  (p a → r)
  . case mpr.inl hpar => apply Exists.intro a hpar
  . admit





example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
constructor
. intro mp_arg
  intro hr
  exact (mp_arg.elim (fun (x:α) => fun (hrpx:r → p x) => Exists.intro x (hrpx hr)))
. intro mpr_arg
  admit


/-

Use tactic combinators to obtain a one line proof of the following:

-/

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat constructor <;> simp [*]
