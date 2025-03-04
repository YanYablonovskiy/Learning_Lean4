import Mathlib.Data.Finset.Basic
import Mathlib.Order.SuccPred.Tree
import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finite.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Countable.Defs
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Data.Set.Function
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Composition

section RandomField

open MeasureTheory
universe u v w x
--The given countable structure indexing the random variables
variable {Γ: Type (u+1)} [Countable Γ]


variable {π:(i:Γ) → Type w}
-- the types (outcome spaces) each site holds; typically always the same


variable {e: Type (v+1)} [E1:MeasurableSpace e] --the given state space, and a measurable space

variable (π':(i:Γ) → e) [E:(i:Γ) → MeasurableSpace (π i)]

#check MeasureTheory.generateFrom_squareCylinders (ι := Γ) (α := fun (i:Γ) ↦ π i)
#check MeasureTheory.cylinderEvents (π := π) (Set.univ: Set Γ)

class RandomFieldSpace' where
 parameter : Type u
 states : (i:parameter) → Type w
 [countable: Countable parameter]
 stateSpaces : (i:parameter) → MeasurableSpace (states i)
 [MeasurableSpace: MeasurableSpace ((i:parameter) → states i)]

variable (N: RandomFieldSpace')

instance (N: RandomFieldSpace'): MeasurableSpace ((i:N.parameter) → N.states i) := MeasurableSpace.pi (π := fun (i:N.parameter) ↦ N.states i) (m:= N.stateSpaces)


--:= MeasurableSpace.pi (π := fun (i:parameter) ↦ states i) (m:= stateSpaces)
structure RandomFieldSpace'' where
mk :: (parameter : Type u) ( states : (i:parameter) → Type w ) (stateSpaces : (i:parameter) → MeasurableSpace (states i)) (MeasurableSpace :=  MeasurableSpace.pi (π := fun (i:parameter) ↦ states i) (m:= stateSpaces))

attribute [instance] RandomFieldSpace'.MeasurableSpace

attribute [instance] RandomFieldSpace'.stateSpaces

--MeasurableSpace := MeasurableSpace.pi (π := fun (i:parameter) ↦ states i) (m:= stateSpaces)
#check RandomFieldSpace'
#check (RandomFieldSpace'.mk Γ π E).MeasurableSpace

#check MeasurableSpace.pi
set_option diagnostics true


--  (a : parameter) → MeasurableSpace ((fun i => states) a)
@[ext]
structure RandomFieldSpace where
 parameter : Type u
 states : Type v
 [countable: Countable parameter]
 stateSpace : MeasurableSpace states
 [MeasurableSpace : MeasurableSpace (parameter → states)]

instance (N: RandomFieldSpace): MeasurableSpace ((N.parameter) → N.states) := MeasurableSpace.pi (π := fun _ ↦ N.states) (m:= fun _ ↦ N.stateSpace)


-- MeasurableSpace := MeasurableSpace.pi  (π := fun (i : parameter) ↦ states) (m:= fun (a : parameter) ↦ by simpa)
#check RandomFieldSpace

#check RandomFieldSpace

#check RandomFieldSpace.mk Γ e E1

attribute [instance] RandomFieldSpace.MeasurableSpace

attribute [instance] RandomFieldSpace.stateSpace
-- instance: Coe (RandomFieldSpace Γ (e := e)) (RandomFieldSpace' (Γ := Γ)) where
--  coe rf := sorry




variable {M: RandomFieldSpace} (Λ: Finset M.parameter) [Nonempty Λ]

#check MeasureTheory.cylinderEvents (π := fun _ ↦ M.states) (Set.univ\(Λ.toSet))


#check @ProbabilityTheory.Kernel (M.parameter → M.states) (M.parameter → M.states) M.MeasurableSpace (MeasureTheory.cylinderEvents (π := fun _ ↦ M.states) (Set.univ\(Λ.toSet)))

#check @ProbabilityTheory.Kernel


structure DependanceType where
 field : RandomFieldSpace
 Specs : (Λ: Finset field.parameter) → @ProbabilityTheory.Kernel (field.parameter → field.states) (field.parameter → field.states) field.MeasurableSpace (MeasureTheory.cylinderEvents (π := fun (i:field.parameter) ↦ field.states) (Set.univ\(Λ.toSet)))

open MeasureTheory

open scoped ENNReal

open ProbabilityTheory

open Kernel

variable (test:DependanceType) (t1 t2: Finset (test.field.parameter)) (ht: t1 ⊆ t2)





#check (test.Specs t1)
#check ProbabilityTheory.Kernel.comp

#check (ProbabilityTheory.Kernel.restrict (test.Specs t2) (s := t1) )
#check @ProbabilityTheory.Kernel.comp (α := test.field.parameter → test.field.states) (β := test.field.parameter → test.field.states) (γ :=  test.field.parameter → test.field.states) (mα := test.field.MeasurableSpace) (mβ :=  (MeasureTheory.cylinderEvents (π := fun _ ↦ test.field.states) (Set.univ\(t1.toSet)))) (mγ :=  (MeasureTheory.cylinderEvents (π := fun _ ↦ test.field.states) (Set.univ\(t2.toSet))))  (test.Specs t2) (test.Specs t1)
--#check (test.Specs t1) ∘ₖ (test.Specs t1)
#check (test.Specs t2)

--#check (test.Specs t1).comp (test.Specs t2)
--#check Specifications M

structure Specification extends DependanceType where
 consistency: ∀Λ₁ Λ₂: Finset field.parameter, (Λ₁ ⊆ Λ₂) → sorry

#check MeasureTheory.generateFrom_squareCylinders
-- #check MeasurableSpace (Set.univ\(Λ.toSet))
-- def σBasis := MeasurableSpace (Set.univ\(Λ.toSet))





end RandomField
