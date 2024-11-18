/- Prove these equivalences: -/

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
have mp: (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
 fun (hAxpnq:∀ x, p x ∧ q x) => And.intro (fun (hx: α) => (hAxpnq hx).1) (fun (hx: α) => (hAxpnq hx).2)
have mpr: (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) :=
 fun (_Axpx_n_Axqx_:(∀ x, p x) ∧ (∀ x, q x)) => (fun (x:α)=> And.intro (_Axpx_n_Axqx_.1 x) (_Axpx_n_Axqx_.2 x))
show (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) from Iff.intro mp mpr



example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
 fun (hAxpxiqx: (∀ x, p x → q x)) => (
  fun (hAxpx:(∀ x, p x)) => (fun (x:α)=>(hAxpxiqx x) (hAxpx x)) --very confusing ((hAxpxiqx x)) is p x → q x, (hAxpx x) is p x
 )




example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
 fun (h:(∀ x, p x) ∨ (∀ x, q x)) =>
  Or.elim h
          (fun (hAx:(∀ x, p x)) => λ(x:α)=>(Or.intro_left (q x) (hAx x)))
          (fun (hAx:(∀ x, q x)) => λ(x:α)=>(Or.intro_right (p x) (hAx x)))
