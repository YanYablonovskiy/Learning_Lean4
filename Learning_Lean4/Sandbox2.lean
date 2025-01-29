import Mathlib.Data.Finset.Basic
import Mathlib.Order.SuccPred.Tree
import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finite.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Countable.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Data.Set.Function
section


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

end


section RandomField

 section Noncanonical
  universe u v
  variable {Γ: Type v} {ε: Type u} --Γ is the countably infinite parameter set
                                                          --ε is the spin Space, and s i is the spin at site i
  open MeasureTheory

  variable [E:MeasurableSpace ε] --[MeasureSpace (Γ → ε)]

  class RandomField' [Countable Γ] where
    randomField_measure := MeasureSpace  (Γ → ε)
    randomField_spin_measurable := E

  #print RandomField'
  end Noncanonical

 section Canonicalold
  universe u v
  variable (Γ: Type v) (ε: Type u) --Γ is the countably infinite parameter set
                                                          --ε is the spin Space, and s i is the spin at site i
  open MeasureTheory

  variable [Countable Γ] [E:MeasurableSpace ε] --[MeasureSpace (Γ → ε)]
  #check Finset.Nonempty

  --collection of finite sub-sets
  abbrev ℐ (S: Type _) :={ s:Finset S | Finset.Nonempty s }

  #synth Countable (ℐ Γ)
  #check (ℐ)
  #check (ℐ Γ)

  --abbrev E := [MeasurableSpace ε]
  #check Finset.toSet
  #check MeasurableSet
  abbrev Ω [Countable Γ] [E:MeasurableSpace ε] := (Γ → ε)

  #check MeasurableSpace.generateFrom

  set_option diagnostics true



  open Function
  --#check { σAinv: Set Γ | ∀T ∈ (ℐ Γ),∀σ,∀A:(σ.range T → E) T ∈ }  --,
  abbrev σTCylinder (t: Finset Γ)  := { (σ:(Ω Γ) ε)  | ∃(g:(Set ε)), (@MeasurableSet ε E g) ∧  σ '' t  = g  }--{ σT: T → ε | ∃A:((ℐ Γ) → E), (σ '' T) ∈ σT } --{} { s:Γ | ∃A:(T → E),} (σ:(Ω Γ) ε)

  #check σTCylinder

  abbrev σTCylinders := { S: Set ((Ω Γ) ε) | ∃t ∈ (ℐ Γ), (σTCylinder Γ ε t)  = S}


  #check MeasurableSpace.generateFrom (σTCylinders Γ ε)

  class RandomField where
   carrier := Γ
   σAlgebra := MeasurableSpace.generateFrom (σTCylinders Γ ε)
   spinSpace := ε
   spinMeasurableSpace := E


 end Canonicalold

end RandomField


section CanonicalRandomField
universe u v
variable (Γ: Type u) (ε: Type v) [Countable Γ] (E:MeasurableSpace ε)

abbrev Ω' {G: Type u} [Countable G] {ε: Type v} := (G → ε)
abbrev F' {G: Type u} [Countable G]: Set (Finset G) := { s:Finset G | Finset.Nonempty s}

abbrev pre_image (k: F' (G:=Γ)): Set (Ω' (ε:=ε) (G:=Γ)) := fun (g:Ω' (G:=Γ)) ↦ @MeasurableSet ε E (g '' (Finset.toSet k))
abbrev pre_images: Set (Set (Ω' (ε:=ε) (G:=Γ))) := fun (k: _) ↦ ∃S:F' (G:=Γ),k = pre_image Γ ε E S
#check pre_image
class RandomField'' where
   carrier := Γ
   σAlgebra := MeasurableSpace.generateFrom (pre_images Γ ε E)
   spinSpace := ε
   spinMeasurableSpace := E

end CanonicalRandomField
