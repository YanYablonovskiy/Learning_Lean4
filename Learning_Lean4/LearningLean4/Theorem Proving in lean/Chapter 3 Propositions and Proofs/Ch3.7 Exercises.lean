/-
Prove the following identities, replacing the "sorry" placeholders with actual proofs.
-/
set_option linter.unusedVariables false
variable {p q r : Prop}

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
have mp: p ∧ q → q ∧ p := --proving p ∧ q → q ∧ p via fun and And.elim , And.intro
 fun (hpnq: p ∧ q) => And.intro hpnq.2 hpnq.1
have mpr: q ∧ p → p ∧ q :=
 fun (hqnp: q ∧ p) => And.intro hqnp.2 hqnp.1
show p ∧ q ↔ q ∧ p from Iff.intro mp mpr


example : p ∨ q ↔ q ∨ p :=
have mp: p ∨ q → q ∨ p :=
 fun (hprq: p ∨ q) => Or.elim
  (hprq)
  (fun (hp:p) => Or.intro_right q hp) -- p → q ∨ p
  (fun (hq:q) => Or.intro_left p hq)  -- q → q ∨ p
have mpr: q ∨ p → p ∨ q :=
 fun (hqrp: q ∨ p) => Or.elim
  (hqrp)
  (fun (hq:q) => Or.intro_right p hq) -- q → p ∨ q
  (fun (hp:p) => Or.intro_left q hp)  -- p → p ∨ q
show p ∨ q ↔ q ∨ p from
 Iff.intro mp mpr

theorem myPropComm : p ∨ q ↔ q ∨ p :=
have mp: p ∨ q → q ∨ p :=
 fun (hprq: p ∨ q) => Or.elim
  (hprq)
  (fun (hp:p) => Or.intro_right q hp) -- p → q ∨ p
  (fun (hq:q) => Or.intro_left p hq)  -- q → q ∨ p
have mpr: q ∨ p → p ∨ q :=
 fun (hqrp: q ∨ p) => Or.elim
  (hqrp)
  (fun (hq:q) => Or.intro_right p hq) -- q → p ∨ q
  (fun (hp:p) => Or.intro_left q hp)  -- p → p ∨ q
show p ∨ q ↔ q ∨ p from
 Iff.intro mp mpr



-- associativity of ∧ and ∨

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
have mp: ((p ∧ q) ∧ r) → (p ∧ (q ∧ r)) :=
 fun (h_pq_r: (p ∧ q) ∧ r) =>
  And.intro (h_pq_r.1).1 (And.intro (h_pq_r.1).2 h_pq_r.2)
have mpr: p ∧ (q ∧ r) → ((p ∧ q) ∧ r) :=
 (fun (hp_qr_:p ∧ (q ∧ r)) =>
  And.intro (And.intro hp_qr_.1 (hp_qr_.2).1) ((hp_qr_.2).2))
show (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) from Iff.intro mp mpr

theorem myPropProdAssoc: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
have mp: ((p ∧ q) ∧ r) → (p ∧ (q ∧ r)) :=
 fun (h_pq_r: (p ∧ q) ∧ r) =>
  And.intro (h_pq_r.1).1 (And.intro (h_pq_r.1).2 h_pq_r.2)
have mpr: p ∧ (q ∧ r) → ((p ∧ q) ∧ r) :=
 (fun (hp_qr_:p ∧ (q ∧ r)) =>
  And.intro (And.intro hp_qr_.1 (hp_qr_.2).1) ((hp_qr_.2).2))
show (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) from Iff.intro mp mpr


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
have mp: (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
 fun (h_prq_rr:(p ∨ q) ∨ r) =>
  Or.elim (h_prq_rr)
          (fun (hprq: (p ∨ q))=>  --need to unfold and prove via p and q
             Or.elim (hprq)
                     (fun (hp:p) => Or.intro_left (q ∨ r) hp)
                     (fun (hq:q) => Or.intro_right p (Or.intro_left r hq)))
          (fun (hr:r) =>
            Or.intro_right p (Or.intro_right q hr))
have mpr: p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
 fun (hpr_qrr_:p ∨ (q ∨ r)) =>
  Or.elim (hpr_qrr_)
          (fun (hp:p)=>
           Or.intro_left r (Or.intro_left q hp))
          (fun (hqrr:q ∨ r) => --need to unfold hqqr and show it follows from q and from r
           Or.elim (hqrr)
                   (fun (hq:q) => Or.intro_left r (Or.intro_right p hq))
                   (fun (hr:r) => Or.intro_right (p ∨ q) hr)
          )
show ((p ∨ q) ∨ r ↔ p ∨ (q ∨ r)) from Iff.intro mp mpr




-- distributivity
--old version
example {p q r: Prop}:p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
have h₁: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := fun (h: p ∧ (q ∨ r)) => --using or elim along with p from h
Or.elim (h.2) (fun (h₂: q) => Or.intro_left (p ∧ r) (And.intro h.1 h₂)) (fun (h₃: r) => Or.intro_right (p ∧ q) (And.intro h.1 h₃))
have h₄: (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := fun (hpqpr:(p ∧ q) ∨ (p ∧ r)) =>
Or.elim (hpqpr) (λ (hpq:p ∧ q) => And.intro hpq.1 (Or.intro_left r hpq.2)) (λ (hpr:p ∧ r) => And.intro hpr.1 (Or.intro_right q hpr.2))
show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) from Iff.intro h₁ h₄





example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have mp: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  fun (hpn_qrr_:p ∧ (q ∨ r)) =>
      Or.elim (hpn_qrr_.2)  --using or elim along with p from hpn_qrr_
              (fun (hq:q) => Or.intro_left ((p ∧ r)) (And.intro hpn_qrr_.1 hq)) --dont need () because of ∧ binding above ∨
              (fun (hr:r) => Or.intro_right (p ∧ q) (And.intro hpn_qrr_.1 hr))
  have mpr: (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) :=
  fun (h_pnq_r_pnr:(p ∧ q) ∨ (p ∧ r)) =>
    Or.elim (h_pnq_r_pnr)
            (fun (hpnq: (p ∧ q)) => And.intro hpnq.1 (Or.intro_left r hpnq.2))
            (fun (hpnr: (p ∧ r)) => And.intro hpnr.1 (Or.intro_right q hpnr.2))
  show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) from Iff.intro mp mpr

--

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
 have mp: p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
   fun (hpr_qnr_:p ∨ (q ∧ r)) =>
    Or.elim (hpr_qnr_)
            (fun (hp:p) => -- p → (p ∨ q) ∧ (p ∨ r)
              And.intro (Or.intro_left q hp)
                        (Or.intro_left r hp))
            (fun (hqnr: q ∧ r) =>
             And.intro (Or.intro_right p hqnr.1)
                       (Or.intro_right p hqnr.2))
 have mpr: (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
   fun (h_prq_n_prr_: (p ∨ q) ∧ (p ∨ r)) =>
    have hprq: p ∨ q := h_prq_n_prr_.1
    have hprr: p ∨ r := h_prq_n_prr_.2
    show p ∨ (q ∧ r) from Or.elim (hprq) -- show p →  p ∨ (q ∧ r) , but more importantly q (and p) implies p ∨ (q ∧ r), and q (and r) implies implies p ∨ (q ∧ r)
                                   (fun (hp:p) => Or.intro_left (q ∧ r) hp)
                                   (fun (hq:q) => (Or.elim (hprr)
                                                           (fun (hp:p)=>Or.intro_left (q ∧ r) hp) -- p (from p ∨ r) →  p ∨ (q ∧ r)
                                                           (fun (hr:r)=>Or.intro_right p (And.intro hq hr)) -- r (from p ∨ r) and q implies p ∧ q and p ∨ (q ∧ r)
                                                  )

                                   )
show p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) from Iff.intro mp mpr

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
 have mp: (p → (q → r)) → (p ∧ q → r) :=
  fun (hpi_qir_:(p → (q → r))) =>
    fun (pnq: p ∧ q) => (hpi_qir_ (pnq.1)) (pnq.2)
 have mpr: (p ∧ q → r) → (p → (q → r)) :=
  fun (h_pnq_ir:(p ∧ q → r)) =>
   fun (hp: p) => fun (hq: q) => (h_pnq_ir (And.intro hp hq)) --applying (p ∧ q) → r to p and q to get r
show (p → (q → r)) ↔ (p ∧ q → r) from Iff.intro mp mpr



example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
 have mp:((p ∨ q) → r) → (p → r) ∧ (q → r) :=
  fun (h_prq_ir:(p ∨ q) → r) =>
   And.intro --first show a p → r
    (fun (hp:p) => h_prq_ir (Or.intro_left q hp))
    (fun (hq:q) => h_prq_ir (Or.intro_right p hq)) -- q → r
have mpr: ((p → r) ∧ (q → r)) → ((p ∨ q) → r) :=
 fun (_pir_n_qir_:((p → r) ∧ (q → r))) =>
  fun (hprq: p ∨ q) => Or.elim hprq (fun (hp:p) => _pir_n_qir_.1 hp) (fun (hq:q) => _pir_n_qir_.2 hq) --use or elim to find functions to r
show ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) from Iff.intro mp mpr



example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
 have mp: ¬(p ∨ q) → ¬p ∧ ¬q :=
  fun (hN_prq_:¬(p ∨ q)) =>
   And.intro (fun (hp:p) => hN_prq_ (Or.intro_left q hp)) -- showing p,q → False via hN_prq_
             (fun (hq:q) => hN_prq_ (Or.intro_right p hq))
 have mpr:  ¬p ∧ ¬q → ¬(p ∨ q) :=
  fun (NpnNq:¬p ∧ ¬q) => (fun (prq:p ∨ q) => Or.elim prq (fun (hp:p) => NpnNq.1 hp) (fun (hq:q) => NpnNq.2 hq)
  )
 show ¬(p ∨ q) ↔ ¬p ∧ ¬q from Iff.intro mp mpr


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
 fun (NprNq:¬p ∨ ¬q) => (fun (pnq: (p ∧ q)) => Or.elim NprNq
                                                       (fun (hnp:¬p)=>hnp (pnq.1)) -- → False in both cases, via applying projections of hpq
                                                       (fun (hnq:¬q)=>hnq (pnq.2))

 )

example : ¬(p ∧ ¬p) :=
 fun (hpnNp:p ∧ ¬p) => hpnNp.2 (hpnNp.1)

example : p ∧ ¬q → ¬(p → q) :=
 fun (hpnNq:p ∧ ¬q) => (fun (piq:p → q) => hpnNq.2 (piq (hpnNq.1)))



example : ¬p → (p → q) :=
 fun (hNp: ¬p) => (fun (hp:p) => @False.elim q (hNp hp)) --using at to show that its implying q



example : (¬p ∨ q) → (p → q) :=
 fun (hNprq: ¬p ∨ q) => fun (hp:p) => Or.elim hNprq
                                              (fun (hNp:¬p)=> @False.elim q (hNp hp))
                                              (fun (hq:q)=>hq)




example : p ∨ False ↔ p :=
 have mp: p ∨ False → p :=
  fun (prF:p ∨ False) => Or.elim prF
                                 (fun (hp:p) => hp)
                                 (fun (F:False) => @False.elim p F)

  have mpr: p → p ∨ False :=
   fun (hp:p) => Or.intro_left False hp
show p ∨ False ↔ p from Iff.intro mp mpr


example : p ∧ False ↔ False :=
 have mp: p ∧ False → False :=
  fun (pnF:p ∧ False) => pnF.2
 have mpr: False → p ∧ False :=
  fun (F:False) => And.intro (@False.elim p F) F
 show p ∧ False ↔ False from Iff.intro mp mpr




example : (p → q) → (¬q → ¬p) :=
 fun (piq: p → q) =>  (fun (hNq:¬q) => (fun (hp:p) => hNq (piq hp))) --contrapositive one direction

--Using non-classical
example : ¬(p ↔ ¬p) :=
 fun (hpINp: p ↔ ¬p) =>
  have hpiF: ¬p := (fun (hp:p) => (hpINp.mp hp) hp)
  have hNpiF: ¬¬p := (fun (hNp:¬p) => hNp (hpINp.mpr hNp))
 show False from hNpiF hpiF


/-
Prove the following identities, replacing the "sorry" placeholders with actual proofs.
These require classical reasoning.
-/


open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
fun (piqrr:p → q ∨ r) =>
have hprNp: p ∨ ¬p :=  Classical.em p
show (p → q) ∨ (p → r) from Or.elim hprNp
                                    (fun (hp:p) => Or.elim (piqrr hp)
                                                           (λ(hq:q)=>Or.intro_left (p → r) (λ(hpp:p) => hq))
                                                           (λ(hr:r)=>Or.intro_right (p → q) (λ(hpp:p) => hr))
                                    )
                                    (fun (hnp:¬p) => Or.intro_left (p → r) (λ(hp:p) => @False.elim q (hnp hp))) --can make p imply anything if ¬p is always true


--demorgans other direction
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
 λ(hNpnq:¬(p ∧ q)) =>
  Or.elim (Classical.em p)
          (λ(hp:p)=> Or.elim (Classical.em q)
                             (λ(hq:q) => @False.elim (¬p ∨ ¬q) (hNpnq (And.intro hp hq)))
                             (λ(hnq:¬q) => Or.intro_right (¬p) (hnq)))
          (λ(hnp:¬p) => Or.intro_left (¬q) hnp)



example : ¬(p → q) → p ∧ ¬q :=
λ(hN_piq_:¬(p → q)) => Or.elim (Classical.em q)
                       (λ(hq:q) => @False.elim (p ∧ (¬q)) (hN_piq_ (λ(hp:p) => hq)))
                       (λ(hNq:¬q) => Or.elim (Classical.em p)
                                            (λ(hp:p) => And.intro hp hNq)
                                            (λ(hNp:¬p) => have hpiq:p → q := (λ(hp:p)=>@False.elim q (hNp hp))
                                                          show p ∧ ¬q from And.intro (@False.elim p (hN_piq_ hpiq)) hNq

                                            ) )





example : (p → q) → (¬p ∨ q) :=
fun (hpiq: p → q) => Or.elim (Classical.em p)
                             (λ(hp:p)=> Or.intro_right (¬p) (hpiq hp))
                             (λ(hNp:¬p)=> Or.intro_left q hNp)

example : (¬q → ¬p) → (p → q) :=         --contrapositive second direction
 fun (hNqiNp:¬q → ¬p) => Or.elim (Classical.em p)
                                 (λ(hp:p) => Or.elim (Classical.em q)
                                                     (λ(hq:q) => (λ(hpp:p) => hq))
                                                     (λ(hNq:¬q) => (λ(hpp:p) => @False.elim q ((hNqiNp hNq) hpp))))
                                 (λ(hNp:¬p) => (λ(hpp:p) => @False.elim q (hNp hpp)))



example : p ∨ ¬p := Classical.em p
example : (((p → q) → p) → p) :=
fun (_prq_rp:(p → q) → p) => Or.elim (Classical.em p)
                                     (λ(hp:p) => hp)
                                     (λ(hNp:¬p) => _prq_rp (λ(hp:p)=>@False.elim q (hNp hp)))
