/-
As a further exercise, we suggest defining boolean operations and, or, not on the Bool type,
and verifying common identities.

Note that you can define a binary operation like and using match:
-/
def and (a: Bool) (b: Bool): Bool :=
 match a with
 | true => b
 | false => false

def and_tactics (a: Bool) (b: Bool): Bool := by
cases a
. exact false
. exact b

def or (a: Bool) (b: Bool): Bool :=
match a with
| true => true
| false => b

def or_tactics (a: Bool)(b: Bool): Bool := by
cases a
. exact b
. exact true


def not (a: Bool): Bool :=
match a with
| true => false
| false => true

def not_tactics (a: Bool): Bool := by
cases a
. exact true
. exact false

/-
As exercises, we encourage you to develop a notion of composition for partial functions from α to β and β to γ,
and show that it behaves as expected.

We also encourage you to show that Bool and Nat are inhabited, that the product
of two inhabited types is inhabited, and that the type of functions to an
inhabited type is inhabited.
-/

universe u v w

def compose_normal {α : Type u} {β : Type v} {γ: Type w} (f: α → β) (g: β → γ): α → γ :=
fun (a:α) => g (f a)

def compose_option {α : Type u} {β : Type v} {γ: Type w} (f: Option α → Option β) (g: Option β → Option γ): Option α → Option γ :=
fun (a:Option α) => g (f a)

/-
As an exercise, prove the following:
-/
theorem append_nil (as : List α) : List.append as nil = as := by
 cases as
 . simp; admit
 . simp; admit

theorem append_assoc (as bs cs : List α)
        : List.append (List.append as bs) cs = List.append as (List.append bs cs) :=
  by simp

theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  Eq.comm.mp h

theorem symm_og {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl


theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by
cases h₁
. assumption


theorem congr_2 {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) := by
cases h
. rfl

/-
Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with pred 0 = 0),
truncated subtraction (with n - m = 0 when m is greater than or equal to n), and exponentiation.

Then try proving some of their basic properties, building on the theorems we have already proved.

Since many of these are already defined in Lean's core library, you should work within a namespace named Hidden,
or something like that, in order to avoid name clashes.
-/

namespace Hidden


--multiplication
def mul (a:Nat)(b:Nat): Nat :=
 match b with
 | Nat.zero => Nat.zero
 | Nat.succ k => (mul a k) + a --for some reason this recursion works


def mul_tac (a:Nat)(b:Nat): Nat := by
cases b
. exact Nat.zero
. case succ k => exact (mul a k) + a


#eval mul 3 4

--the predecessor function (with pred 0 = 0)

def pred (a:Nat): Nat :=
match a with
| Nat.zero => Nat.zero
| Nat.succ k => k

def pred_tactic (a: Nat): Nat := by
cases a
. exact Nat.zero
. assumption


#eval pred 6

#eval pred_tactic 6

--truncated subtraction (with n - m = 0 when m is greater than or equal to n)

-- def trunc_sub (n: Nat)(m: Nat): Nat := by
-- cases m
-- . exact n
-- . case succ k => exact trunc_sub n (pred k)



def exp (n: Nat)(m: Nat): Nat :=
match m with
| Nat.zero => Nat.succ (Nat.zero)
| Nat.succ k => mul (exp n k) n--n^(k+1) ; recursion worked this time

def exp_tactic (n: Nat)(m: Nat): Nat := by
cases m
. exact Nat.succ (Nat.zero)
. case succ k => exact mul (exp n k) n

/-
Define some operations on lists, like a length function or the reverse function.

Prove some properties, such as the following:

a. length (s ++ t) = length s + length t

b. length (reverse t) = length t

c. reverse (reverse t) = t
-/

variable {α: Type u}

def length (as: List α): Nat :=
 match as with
 | List.nil => Nat.zero
 | List.cons _ ks => Nat.succ (length ks)

def length_tactic (as: List α): Nat := by
cases as
. exact Nat.zero
. case cons head tail => exact Nat.succ (length_tactic tail)



def reverse (as: List α): List α :=
match as with
| List.nil => List.nil
| List.cons a bs => sorry

def reverse_tactic (as: List α): List α := by
cases as
. exact List.nil
. case cons head tail => admit



-- example (s: List α) (t: List α): length (s ++ t) = length s + length t :=
-- match t with
-- | List.nil => sorry
--  sorry

/-
Define an inductive data type consisting of terms built up from the following constructors:

const n, a constant denoting the natural number n
var n, a variable, numbered n
plus s t, denoting the sum of s and t
times s t, denoting the product of s and t

Recursively define a function that evaluates any such term with respect to
an assignment of values to the variables.
-/
inductive Terms where
|const: Nat → Terms
