/-
Well-Founded Recursion and Induction:

When structural recursion cannot be used, we can prove termination using
well-founded recursion.

We need a well-founded relation and a proof that each recursive application
is decreasing with respect to this relation.

Dependent type theory is powerful enough to encode and justify
well-founded recursion.

Let us start with the logical background that is needed to understand
how it works.

Lean's standard library defines two predicates,
Acc r a and WellFounded r, where r is a binary relation on a type α, and a
is an element of type α.

-/

variable (α : Sort u)
variable (r : α → α → Prop)
variable (x: α)
#check (Acc r : α → Prop)
#check (WellFounded r : Prop)

#check Acc r
#check Acc r x --essentially locking in the first argument for r
#check Acc
#check WellFounded
#check WellFounded r



/-
The first, Acc, is an inductively defined predicate.

According to its definition, Acc r x is equivalent to ∀ y, r y x → Acc r y.

If you think of r y x as denoting a kind of order relation y ≺ x,
then Acc r x says that x is accessible from below, in the sense that
all its predecessors are accessible.

In particular, if x has no predecessors, it is accessible.

Given any type α, we should be able to assign a value to each
accessible element of α, recursively, by assigning values to
all its predecessors first.

The statement that r is well-founded, denoted WellFounded r,
is exactly the statement that every element of the type is accessible.

By the above considerations, if r is a well-founded relation on a type α,
we should have a principle of well-founded recursion on α, with respect
to the relation r.

And, indeed, we do: the standard library defines WellFounded.fix,
which serves exactly that purpose.
-/
noncomputable def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x) -- given for y < x, C y; we get C x
      : (x : α) → C x := WellFounded.fix h F

/-
There is a long cast of characters here, but the first block we have already 
seen: the type, α, the relation, r, and the assumption, h, that r is 
well-founded. 

The variable C represents the motive of the recursive definition: for each element x : α, we would like to 
construct an element of C x. 

--induction but not for prop

The function F provides the inductive recipe for doing that: it tells us how to construct an element C x, 
given elements of C y for each predecessor y of x.

Note that WellFounded.fix works equally well as an induction principle. 

--if C x is a prop:

It says that if ≺ is well-founded and you want to prove ∀ x, C x, it suffices to show that 
for an arbitrary x, if we have ∀ y ≺ x, C y, then we have C x(given the inductive hypothesis).


In the example above we use the modifier noncomputable because the code generator 
currently does not support WellFounded.fix. 

The function WellFounded.fix is another tool Lean uses to justify that a function terminates.

Lean knows that the usual order < on the natural numbers is well founded. 

It also knows a number of ways of constructing new well founded orders from others, for example, 
using lexicographic order.

Here is essentially the definition of division on the natural numbers that is found in the standard library.
-/

open Nat

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else
    zero


noncomputable def div' := WellFounded.fix (measure id).wf div.F

#reduce div' 8 2 -- 4

/-
The definition is somewhat inscrutable. 

Here the recursion is on x, and div.F x f : Nat → Nat returns the "divide by y" function for that fixed x. 

You have to remember that the second argument to div.F, the recipe for the recursion, is a function that is 
supposed to return the divide by y function for all values x₁ smaller than x.

The elaborator is designed to make definitions like this more convenient. It accepts the following:
-/

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div (x - y) y + 1
  else
   0

--basically keeps reducing by factors of y, counting each factor until below x


#reduce div


/-
When Lean encounters a recursive definition, it first tries structural recursion, and only when that fails, 
does it fall back on well-founded recursion. 

Lean uses the tactic decreasing_tactic to show that the recursive applications are smaller. 

The auxiliary proposition x - y < x in the example above should be viewed as a hint for this tactic.

The defining equation for div does not hold definitionally, but we can unfold div using the unfold tactic. 

We use conv to select which div application we want to unfold.
-/

example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div;  -- unfold occurrence in the left-hand-side of the equation
  rfl

example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]

/-
The following example is similar: it converts any natural number to a binary expression, 
represented as a list of 0's and 1's. 

We have to provide evidence that the recursive call is decreasing, which we do here with a sorry. 

The sorry does not prevent the interpreter from evaluating the function successfully.
-/
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval! natToBin 1234567 --[1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1]

/-
As a final example, we observe that Ackermann's function can be defined directly, because it is 
justified by the well-foundedness of the lexicographic order on the natural numbers. 

The termination_by clause instructs Lean to use a lexicographic order. 

This clause is actually mapping the function arguments to elements of type Nat × Nat. 

Then, Lean uses typeclass resolution to synthesize an element of type WellFoundedRelation (Nat × Nat).
-/
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)

--structural recursion available?

def ack' : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

#reduce ack
#reduce ack' --uses structural

/-
Note that a lexicographic order is used in the example above because the instance WellFoundedRelation (α × β) 
uses a lexicographic order. Lean also defines the instance:
-/
instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel

/-
In the following example, we prove termination by showing 
that as.size - i is decreasing in the recursive application.
-/


variable (α : Type u) 

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩ --gets the ith value, with proof its permissable
      if p a then --if p is true of the ith value a
        go (i+1) (r.push a) --go to next step of loop; and get rid of a from r
      else
        r
    else
      r
  termination_by as.size - i --as the size gets lower,relation of Nat

/-
 Note that, auxiliary function go is recursive in this example, but takeWhile is not.

 By default, Lean uses the tactic decreasing_tactic to prove recursive applications are decreasing. 
 
 The modifier decreasing_by allows us to provide our own tactic. Here is an example.
-/

theorem div_lemma' {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div'' (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div'' (x - y) y + 1
  else
    0
  decreasing_by apply div_lemma'; assumption

/-
Note that decreasing_by is not replacement for termination_by, they complement each other. 
termination_by is used to specify a well-founded relation, and decreasing_by for providing our own tactic 
for showing recursive applications are decreasing. --in that order

In the following example, we use both of them.
-/

def ack'' : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack'' x 1
  | x+1, y+1 => ack'' x (ack'' (x+1) y)
termination_by x y => (x, y)
decreasing_by
  all_goals simp_wf -- unfolds well-founded recursion auxiliary definitions
  · apply Prod.Lex.left; simp_arith
  · apply Prod.Lex.right; simp_arith
  · apply Prod.Lex.left; simp_arith

  /-
  We can use decreasing_by sorry to instruct Lean to "trust" us that the function terminates.
  -/


def natToBin' : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin' ((n + 2) / 2) ++ [n % 2]
decreasing_by sorry

#eval! natToBin' 1234567

/-
Recall that using sorry is equivalent to using a new axiom, and should be avoided. 

In the following example, we used the sorry to prove False. 

The command #print axioms unsound shows that unsound depends on the unsound axiom sorryAx used to 
implement sorry
-/
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` is a proof of `False`

#print axioms unsound
-- 'unsound' depends on axioms: [sorryAx]

/-
Summary:

If there is no termination_by, a well-founded relation is derived (if possible) by selecting an argument 
and then using typeclass resolution to synthesize a well-founded relation for this argument's type.

If termination_by is specified, it maps the arguments of the function to a type α and type class resolution 
is again used. 

Recall that, the default instance for β × γ is a lexicographic order based on the well-founded relations 
for β and γ.

The default well-founded relation instance for Nat is <.

By default, the tactic decreasing_tactic is used to show that recursive applications are smaller
with respect to the selected well-founded relation. 
 
If decreasing_tactic fails, the error message includes the remaining goal ... |- G. 

Note that, the decreasing_tactic uses assumption. 

So, you can include a have-expression to prove goal G. 

You can also provide your own tactic using decreasing_by.
-/

