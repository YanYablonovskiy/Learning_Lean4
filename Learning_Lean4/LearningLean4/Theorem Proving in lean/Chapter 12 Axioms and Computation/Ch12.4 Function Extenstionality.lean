/-
Function Extensionality:

Similar to propositional extensionality, function extensionality asserts
that any two functions of type (x : α) → β x that agree on all their
inputs are equal:
-/

namespace ex

universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

/-
The statement is:

(∀ (x : α), f x = g x)
         → f = g)
-/


#print funext


/-
From a classical, set-theoretic perspective, this is exactly what it
means for two functions to be equal.

This is known as an "extensional" view of functions.

From a constructive perspective, however, it is sometimes more natural
to think of functions as algorithms, or computer programs, that are
presented in some explicit way.

It is certainly the case that two computer programs can compute the same
answer for every input despite the fact that they are syntactically
quite different.

In much the same way, you might want to maintain a view of functions
that does not force you to identify two functions that have the same
input / output behavior.

This is known as an "intensional" view of functions.

In fact, function extensionality follows from the existence of
quotients, which we describe in the next section.

In the Lean standard library, therefore, funext is thus proved from
the quotient construction.

Suppose that for α : Type we define
the Set α := α → Prop to denote the type of subsets of α,
essentially identifying subsets with predicates.

By combining funext and propext, we obtain an extensional theory of
such sets:
-/


def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))


--since sets are essentially functions


/-
We can then proceed to define the empty set and set intersection,
for example, and prove set identities:
-/
def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h) --from a ∩ a to a
    (fun h => ⟨h, h⟩) --from a to a ∩ a

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h) --from a ∩ ∅ to ∅
    (fun h => False.elim h)--from ∅ to a ∩ ∅

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)

/-
The following is an example of how function extensionality blocks
computation inside the Lean kernel:
-/
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val


/-
First, we show that the two functions f and g are equal using function extensionality,
and then we cast 0 of type Nat by replacing f by g in the type.

Of course, the cast is vacuous, because Nat does not depend on f.

But that is enough to do the damage: under the computational rules of the system,
we now have a closed term of Nat that does not reduce to a numeral.

In this case, we may be tempted to reduce the expression to 0.

But in nontrivial examples, eliminating cast changes the type of the term,
which might make an ambient expression type incorrect.

The virtual machine, however, has no trouble evaluating the expression to 0.

Here is a similarly contrived example that shows how propext can get in the way:
-/

theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val' : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val'

-- evaluates to 0
#eval val'

/-
Current research programs, including work on observational type theory
and cubical type theory, aim to extend type theory in ways that permit
reductions for casts involving function extensionality, quotients, and more.

But the solutions are not so clear-cut, and the rules of Lean's underlying calculus
do not sanction such reductions.

In a sense, however, a cast does not change the meaning of an expression.

Rather, it is a mechanism to reason about the expression's type.

Given an appropriate semantics, it then makes sense to reduce terms in ways that
preserve their meaning, ignoring the intermediate bookkeeping needed to make
the reductions type-correct.

In that case, adding new axioms in Prop does not matter; by proof irrelevance,
an expression in Prop carries no information, and can be safely ignored by
the reduction procedures.
-/



end Set
end ex
