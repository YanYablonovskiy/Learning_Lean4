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


--exersises after finishing chapter fully:

/-
Prove these equivalences:
-/
variable (α : Type) (p q : α → Prop)
--v1
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
 have mp: (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := fun ( hAxpxnqx:(∀ x, p x ∧ q x)) =>
                                                         And.intro (fun (x:α)=> (hAxpxnqx x).1) (fun (x:α)=> (hAxpxnqx x).2)
 have mpr: ((∀ x, p x) ∧ (∀ x, q x)) → (∀ x, p x ∧ q x)  := fun  h: (∀ x, p x) ∧ (∀ x, q x) => (fun (x:α) => And.intro (h.1 x) (h.2 x))
 show (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) from Iff.intro mp mpr

--short version
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
 fun h1:_ => fun h2:_ => fun x:_ => (h1 x) (h2 x)

--short version
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
fun h:_ => h.elim (fun h1:_ => fun x:_ =>( Or.intro_left (q x) (h1 x))) (fun h2:_ => fun x:_ => Or.intro_right (p x) (h2 x))

/-
You should also try to understand why the reverse implication is not derivable in the last example.


It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable.

Try proving these (one direction of the second of these requires classical logic):
-/
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
fun a:α =>
 have mp: (∀ x : α, r) → r :=
            fun f:_ => f a
 have mpr: r → (∀ x : α, r) :=
  fun hr:_  => fun _ => hr
 show (∀ x : α, r) ↔ r from Iff.intro mp mpr


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
 have mp:(∀ x, p x ∨ r) → (∀ x, p x) ∨ r := fun h1:_ => Or.elim (Classical.em r) (fun h2:_ => Or.intro_right (∀ x, p x) h2)
                                                   (fun h3:_ => Or.intro_left r (fun x:α => ((h1 x).elim (fun px:p x => px) (fun hr:r => @False.elim (p x) (h3 hr)))))
                                                                                                                                              
 have mpr:(∀ x, p x) ∨ r →  (∀ x, p x ∨ r) :=
  fun p₁:_ => p₁.elim (fun (q₁:_) => fun (x:α) => Or.intro_left r (q₁ x)) (fun (q₂:r) => fun (x:α) => Or.intro_right (p x) q₂)
 show (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r from Iff.intro mp mpr




example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
 have mp: (∀ x, r → p x) → (r → ∀ x, p x) :=
  fun (a:_) => fun (hr:r) => fun (x:α) => (a x) hr
 have mpr: (r → ∀ x, p x) → (∀ x, r → p x) :=
  fun (b:_) => fun (x:α) => fun (hr:r) => (b hr) x
 show (∀ x, r → p x) ↔ (r → ∀ x, p x) from Iff.intro mp mpr

/-
Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves.

Prove that this is a contradiction:
-/
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
have h₁: shaves barber barber ↔  ¬ shaves barber barber := h barber
let p:=shaves barber barber;
have hnp: ¬p := fun (hp:p) => (h₁.mp hp hp)
have hnnp: ¬¬p := fun (hnp₁:¬p) => hnp (h₁.mpr hnp₁)
show False from hnnp hnp
/-
Remember that, without any parameters, an expression of type Prop is just an assertion.

Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions.

For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n.

Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes.

Look up the definition of a Fermat prime or any of the other statements, if necessary.
-/
def even (n : Nat) : Prop := ∃(k:Nat),n=2*k

def prime (n : Nat) : Prop := ¬(∃(k l:Nat),n=k*l ∧ (k >1) ∧ (l > 1) ∧ (k < n) ∧ (l < n))

def infinitely_many_primes : Prop := ¬ (∃(P:Nat),(prime P) ∧ (∀(p:Nat),prime p → (p < P)))

def Fermat_prime (n : Nat) : Prop := (prime n) ∧ (∃(k:Nat),n = 2^k + 1)

def infinitely_many_Fermat_primes : Prop := ¬ (∃(P:Nat),(Fermat_prime P) ∧ (∀(p:Nat),Fermat_prime p → (p < P)))

def goldbach_conjecture : Prop := ∀(n:Nat),((even n ∧ (n > 2)) → (∃(k l:Nat),(prime k ∧ prime l) ∧ (n = k+l)))

def Goldbach's_weak_conjecture : Prop := ∀(n:Nat),((¬(even n) ∧ (n > 5)) → (∃(k l m:Nat),((prime k) ∧ (prime l) ∧ prime m) ∧ (n = k+l+m)))

def Fermat's_last_theorem : Prop := ∀(n:Nat),((n ≥ 4) → ¬(∃(x y z: Nat),x^n+y^n=z^n))
/-
Prove as many of the identities listed in the Existential Quantifier section as you can.

-/

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

--since r doesnt depend on x (or α);
example : (∃ x : α, r) → r :=
fun h:_ => h.elim ( fun (x:α) => fun(hr:r) => hr)


example (a : α) : r → (∃ x : α, r) :=
 fun (hr:r) => Exists.intro a hr


-- again, r inhabitation doesnt depend on the specific value of x

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
 have mp: (∃ x, p x ∧ r) → (∃ x, p x) ∧ r :=
  fun h₁:_ => h₁.elim (fun (h₂:α)(h₄:p h₂ ∧ r) => And.intro (Exists.intro h₂ h₄.1) h₄.2)
 have mpr: (∃ x, p x) ∧ r → (∃ x, p x ∧ r) :=
  fun h₃:_ => Exists.elim h₃.1 (fun (x:α) => fun (h₅: p x) => ( Exists.intro x (And.intro h₅ h₃.2)))
 show (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r from Iff.intro mp mpr


--back direction likely needs classical (didnt)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
 have mp:(∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) :=
  fun (h:_) => h.elim (fun (x:α) => fun (hpq:p x ∨ q x) => hpq.elim (fun (p:p x) => Or.intro_left (∃ x, q x) (Exists.intro x p)) (fun (q:q x) => Or.intro_right (∃ x, p x) (Exists.intro x q)))
 have mpr: (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x) :=
  fun h:_ => h.elim (fun h₁:_ => h₁.elim (fun (x:α)(px: p x) => ⟨x,Or.inl px⟩)) (fun h₂:_ => h₂.elim (fun (x:α)(qx: q x) => ⟨x,Or.inr qx⟩))
 show (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) from Iff.intro mp mpr

--will need classical
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
have mp: (∀ x, p x) → ¬ (∃x, ¬ p x) :=
 fun h₁:_ =>
  fun h₂:(∃x, ¬ p x)=>
   h₂.elim (fun (a:α) => fun (hnpa:¬p a) => hnpa (h₁ a))
have mpr:  ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
 fun b₁:_  =>
  fun (x:α) => (Classical.em (p x)).elim (fun (b₁₁:p x) => b₁₁)
               (fun (b₁₂:¬p x) => False.elim (b₁ ⟨x,b₁₂⟩))
show (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) from Iff.intro mp mpr


example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
 have mp: (∃x, p x) → ¬ (∀ x, ¬ p x) :=
  fun f₁:_ =>
   f₁.elim (fun x => fun f₁₁:(p x) => (fun f₁₁₁: (∀ x, ¬ p x) =>  (f₁₁₁ x) f₁₁))
 have mpr: ¬ (∀ x, ¬ p x) → (∃x, p x) :=
  fun b₁:_ =>
    have b₁₁:¬¬(∃x, p x) :=
    fun b₂:¬(∃x, p x) => b₁ (fun (x:α)(hp: p x) => ( b₂ (Exists.intro x (hp)) ) )
    show (∃x, p x) from (Classical.em (∃x, p x)).elim (fun b₂₁:(∃x, p x)=>b₂₁) (fun b₂₂:_ => False.elim (b₁₁ b₂₂))
 show (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) from Iff.intro mp mpr



example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
 have mp:(¬ ∃ x, p x) → (∀ x, ¬ p x) :=
  fun f₁:_ => fun (x:α) => fun (hpx: p x) => f₁ (Exists.intro x hpx)
 have mpr: (∀ x, ¬ p x) → (¬ ∃ x, p x) :=
  fun b₁:_ => fun b₁₁: ∃ x, p x => b₁₁.elim (fun x => fun hpx:_ => b₁ x hpx)
show (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) from Iff.intro mp mpr


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
have mp: (¬ ∀ x, p x) → (∃ x, ¬ p x) :=
 fun (f₁:(¬ ∀ x, p x)) => (Classical.em  (∀ x, p x)).elim
                          (fun l:_ => False.elim (f₁ l))
                          (sorry)
have mpr: (∃ x, ¬ p x) → (¬ ∀ x, p x) :=
 fun (b₁:_) => ( fun (hax: ∀ x, p x) => Exists.elim b₁ (fun x => fun hx => hx (hax x)) )
show (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) from Iff.intro mp mpr

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
have mp: (∀ x, p x → r) → (∃ x, p x) → r :=
 fun f₁:_ => fun (f₁₁:(∃ x, p x)) => f₁₁.elim ( λ x => λ px => (f₁ x) px)
have mpr: ((∃ x, p x) → r) → (∀ x, p x → r) :=
 fun b₁:_ => fun (x:α) => fun (hp: p x) => b₁ (Exists.intro x hp)
show  (∀ x, p x → r) ↔ (∃ x, p x) → r from Iff.intro mp mpr


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
have mp:(∃ x, p x → r) → (∀ x, p x) → r :=
 fun f₁:_ => fun f₂:_ => f₁.elim fun (x:α) => fun (h:_) => h (f₂ x)
have mpr:((∀ x, p x) → r) → (∃ x, p x → r) :=
 fun b₁: ((∀ x, p x) → r) => sorry
 
show (∃ x, p x → r) ↔ (∀ x, p x) → r from Iff.intro mp mpr


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
 have mp:(∃ x, r → p x) → r → ∃ x, p x :=
  fun f₁:(∃ x, r → p x) => fun hr:r => f₁.elim (λ x => λ rpx => Exists.intro x (rpx hr))
 have mpr: (r → ∃ x, p x) → (∃ x, r → p x) :=
  fun b₁₁:_ => sorry
 show (∃ x, r → p x) ↔ (r → ∃ x, p x) from Iff.intro mp mpr


#check Int.le_add_one
#check Int.le_refl
#check Int.le_add_of_nonneg_left
#check Int.ofNat_succ_pos
