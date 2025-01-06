
import Mathlib.Data.Finset.Basic
import Mathlib.Order.SuccPred.Tree
import Mathlib.Data.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
set_option linter.docPrime false
universe v






variables {M: Finset α} {T : SimpleGraph M} (h : T.IsAcyclic)

#check Nat.find (H:= LE.le.exists_pred_iterate _)

#check IsPredArchimedean
#print IsPredArchimedean

--variable (α: Type v) (A: Set A)
--variable [SA: SemilatticeInf A] [OA: OrderBot A] [PA :PredOrder A]
--variable [IPA: IsPredArchimedean A]

inductive BinTree: Type u where
 | root : BinTree
 | node : BinTree → (BinTree → BinTree)


variable (α: Type u) (tb: BinTree)  [sa: SemilatticeInf ↑α]
[r: PartialOrder ↑α]

#check BinTree.root

#check sa.inf_le_left

variable {t: RootedTree} [IA: Infinite t]
variable (r : t.α)

#check t.subtree


#check t.predOrder
#check t.α

#check PredOrder
#print PredOrder

#check Preorder
#print Preorder

#check RootedTree.mk
#check OrderBot
#check RootedTree
#print RootedTree

/-

structure RootedTree.{u_2} : Type (u_2 + 1)
number of parameters: 0
constructor:
RootedTree.mk : (α : Type u_2) →
  [semilatticeInf : SemilatticeInf α] →
    [orderBot : OrderBot α] → [predOrder : PredOrder α] → [isPredArchimedean : IsPredArchimedean α] → RootedTree
fields:
α : Type u_2
semilatticeInf : SemilatticeInf ↑self
orderBot : OrderBot ↑self
predOrder : PredOrder ↑self
isPredArchimedean : IsPredArchimedean ↑self
-/



#synth Preorder Nat
#check Preorder Nat
#check PredOrder Nat

#synth SemilatticeInf Nat
--#check RootedTree.mk Nat




instance: PredOrder Nat where
 pred := fun (n: Nat) =>
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
 pred_le := by intro a; cases a with
 | zero => rfl
 | succ _ => simp
 min_of_le_pred := by intro a; cases a with
 | zero => simp
 | succ _ => simp
 le_pred_of_lt := by intro a; cases a with
 | zero => simp
 | succ k => simp_arith; intro b; cases b with
  | zero => intro k; contradiction
  | succ m => simp; apply Nat.succ_le_of_lt

#synth PredOrder Nat



instance: Bot Nat where
bot := Nat.zero

instance: OrderBot Nat where
bot_le := by intro a; simp

#check RootedTree.mk Nat

variable (NTree: (RootedTree.mk Nat))

#check OrderBot Nat
#check Bot Nat
#check (inferInstance: Bot Nat)


#eval (Bot.bot: Nat)




#print SemilatticeInf


/-
Class SemilatticeInf.{u} : Type u → Type u
number of parameters: 1
constructor:
SemilatticeInf.mk : {α : Type u} →
  [toInf : Inf α] →
    [toPartialOrder : PartialOrder α] →
      (∀ (a b : α), a ⊓ b ≤ a) →
        (∀ (a b : α), a ⊓ b ≤ b) → (∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c) → SemilatticeInf α
fields:
toInf : Inf α
toPartialOrder : PartialOrder α
inf_le_left : ∀ (a b : α), a ⊓ b ≤ a
inf_le_right : ∀ (a b : α), a ⊓ b ≤ b
le_inf : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c
-/

#check SemilatticeInf
#print Inf
#check OrderBot
#check Finset
#print OrderBot
/-
class OrderBot.{u} : (α : Type u) → [inst : LE α] → Type u
number of parameters: 2
constructor:
OrderBot.mk : {α : Type u} → [inst : LE α] → [toBot : Bot α] → (∀ (a : α), ⊥ ≤ a) → OrderBot α
fields:
toBot : Bot α
bot_le : ∀ (a : α), ⊥ ≤ a
-/
#check Bot.bot
#check RootedTree.orderBot
#check LE
#print LE

def IsCutset (S: Finset t.α): Prop :=
 (∀ v:t.α, (∃p:S,p ≤ v ∨ p ≥ v))

def IsCutset' {t: RootedTree} (S: Finset t.α): Prop :=
(∀ v:t.α, (∃p:S,p ≤ v ∨ p ≥ v))

-- def Depth (v: t.α): Nat := by
--  let r := t.orderBot.bot;
--  let j := 0;
--  let rec loop: Nat → t.α


#check IsCutset

#check RootedTree.mk Nat
#check @IsCutset' (RootedTree.mk Nat)

#check inferInstance
theorem numberisCutset  (n: Nat): @IsCutset (RootedTree.mk Nat) {n} := by
 intro NC; simp; cases n
 . case zero => simp
 . case succ j => apply Nat.le_or_ge

instance: Inhabited RootedTree where
default := RootedTree.mk Nat

#check @numberisCutset

variable (S5: Finset α)
#check sizeOf
#check sizeOf S5
#check bot_le
variable (r:t.α)
#check _^[_]
#check _^_
#check Order.pred^[5]
--#check @Nat.find exists_pred_iterate_or (bot_le (a := r))
--Nat.find (bot_le (a := r)).exists_pred_iterate
--#check Nat.find (Exists.intro ) (bot_le (a := r))
#check IsCutset
#check {A:Finset t.α | IsCutset A}
variable [DecidableEq t.α]
open IsPredArchimedean

#check Nat.find (bot_le (a := r)).exists_pred_iterate
variable (NC: RootedTree.mk ℕ)
variable (x:{A:Finset t | IsCutset A})
variable (x1:{A:Finset t.α | IsCutset A})

def TreeDistance (a: t.α) (b: t.α): Nat := by
let r := t.semilatticeInf.inf a b;
admit


def depth (a: t.α): Nat :=
 Nat.find (bot_le (a := a)).exists_pred_iterate


#check @depth


def Udistance (v₁ : t.α) (v₂ : t.α) (h: v₁ ≤ v₂): Nat :=
 sorry


def d {t:RootedTree} (v:t.α): Real := 1

#check @Subtype (Finset t.α) (IsCutset )

variable (P:{A:Finset t.α // IsCutset A}) (P1:{A:Finset t.α | IsCutset A})

#check P1.mem


def BranchingNumber (t: RootedTree) [m: SizeOf (t.α)]: Real := by
let All_Cutsets :=  {A:Finset t.α | IsCutset A};
let Cutset_Sum (l: Real) (X: Finset (t.α)) (hc: IsCutset X): Real :=
 Finset.sum X d;
admit
