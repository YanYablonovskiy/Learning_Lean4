import Mathlib.Data.Finset.Basic
import Mathlib.Order.SuccPred.Tree
import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finite.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

variable {T: RootedTree}


#check OrderBot.bot_le
#check LE.le.exists_pred_iterate (OrderBot.bot_le (_:T.α))

def Cutset (S: Finset T.α): Prop :=
 ∀(v: T.α),(∃(z:S),(v ≤ z ∨ z ≤ v))


def Cutset': (S: Finset T.α) →  Prop :=
 fun S => ∀(v: T.α),(∃(z:S),(v ≤ z ∨ z ≤ v))

def Cutset_sum (f:T.α → ℝ) (S: Finset T.α): ℝ :=
 S.sum f

noncomputable def Depth (v: T.α): ℕ :=
 Classical.choose (LE.le.exists_pred_iterate (OrderBot.bot_le v))

noncomputable def Cutset_exponent (S: Finset T.α) (b: ℝ): ℝ  :=
 Cutset_sum (fun (v:T.α) => (b^(-1:Int))^(Depth v)) S


noncomputable def Cutset_exponent' (S: Finset T.α) (HS:Cutset S) (b: ℝ): ℝ  :=
 Cutset_sum (fun (v:T.α) => (b^(-1:Int))^(Depth v)) S

variable (k:ℝ)  (Cutset_Set: { S: Finset T.α | Cutset S})

#check Cutset_exponent (b:=k)
#check Cutset_Set.map (Cutset_exponent (b:=k)) (h:=_) (q:= fun x:ℝ => x >0) (p:= fun _ => Cutset _)
#check Cutset_Set.map

noncomputable def CutsetSumSeq (f:T.α → ℝ) (S: Nat → Finset T.α) (hC: ∀n, Cutset (S n)): ℕ → ℝ :=
 fun (m:Nat) => Cutset_sum f (S m)

noncomputable def CutsetExpSumSeq (S: Nat → Finset T.α) (hC: ∀n, Cutset (S n)): ℝ → (ℕ → ℝ) :=
 fun (e:ℝ) => fun (m:ℕ) => Cutset_exponent (b:=e) (S m)

#check iInf
#print iInf

#check Set.mapsTo_range
#check Set.mapsTo'
#check Set.range
#check Set
#print Set

#check Set (Finset T.α)
#check Cutset
#check Set (Finset T.α)
#check Cutset'
#print Set
#check Set

def Cutset'': Set (Finset T.α) :=
 fun S => ∀(v: T.α),(∃(z:S),(v ≤ z ∨ z ≤ v))


#check Cutset''
#check Set Cutset''
def InfGTZero (e:ℝ) (S: Nat → Finset T.α) (hC: ∀n, Cutset (S n)) : Prop :=
 iInf ((CutsetExpSumSeq S hC) e) > 0

def InfGTZeroCutsets (e:ℝ): Prop :=
 sorry--let Vals := fun H1: Set Cutset'' => H1.map (Cutset_exponent' S HS e); sInf (Set.range Vals) > (0:ℝ)

def GTZeroSet  (S: Nat → Finset T.α) (hC: ∀n, Cutset (S n)): Set ℝ :=
{ (x:ℝ) | InfGTZero x S hC}

variable {CutSetSeqs: Nat → Finset T.α}   (hC: ∀n, Cutset (CutSetSeqs n))

noncomputable def BranchingNumber: ℝ :=
 SupSet.sSup (GTZeroSet CutSetSeqs hC)

#check BranchingNumber



#check SupSet.sSup (GTZeroSet CutSetSeqs hC)

--need Inf over e, where inf over cutsets



#check iInf (CutsetSumSeq _ _ _)
