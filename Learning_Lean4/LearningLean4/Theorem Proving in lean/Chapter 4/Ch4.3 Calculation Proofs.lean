/-
A calculational proof is just a chain of intermediate results that are meant to be
composed by basic principles such as the transitivity of equality.

In Lean, a calculational proof starts with the keyword calc, and has the following syntax:
-/

/-

calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
  '_'       'op_2'  <expr>_2  ':='  <proof>_2
  ...
  '_'       'op_n'  <expr>_n  ':='  <proof>_n


-/


/-
Note that the calc relations all have the same indentation.

Each <proof>_i is a proof for <expr>_{i-1} op_i <expr>_i.

--Each <proof>_i is a proof for <expr>_{i-1} op_i <expr>_i., meaning in totality we start with expr_0
-- then after all steps obtain a proof via expr_0 op_1 expr_1 op_2 expr_2... expr_n
-- meaning in totality expr_0 op_1 expr_n (if it is transitive)


We can also use _ in the first relation (right after <expr>_0) which is useful to
align the sequence of relation/proof pairs:

-/


/-
calc <expr>_0
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
-/

/-
Here is an example:
-/

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

example : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

theorem T (a b c d e : Nat)(h1 : a = b)(h2 : b = c + 1)(h3 : c = d)(h4 : e = 1 + d): a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

/-
This style of writing proofs is most effective when it is used in conjunction with the simp and rewrite tactics,
which are discussed in greater detail in the next chapter.

For example, using the abbreviation rw for rewrite, the proof above could be written as follows:
-/

example : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

--my version, no tactics
example : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg _ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

/-
Essentially, the rw tactic uses a given equality (which can be a hypothesis, a theorem name,
or a complex term) to "rewrite" the goal.

If doing so reduces the goal to an identity t = t, the tactic applies reflexivity to prove it.

Rewrites can be applied sequentially, so that the proof above can be shortened to this:
-/
example : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

/-
Or even this:
-/
example: a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

/-
The simp tactic, instead, rewrites the goal by applying the given identities
repeatedly, in any order, anywhere they are applicable in a term.

It also uses other rules that have been previously declared to the system,
and applies commutativity wisely to avoid looping.

As a result, we can also prove the theorem as follows:
-/
example : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
/-
We will discuss variations of rw and simp in the next chapter.

The calc command can be configured for any relation that supports some form of transitivity.
It can even combine different relations.
-/
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

/-
You can "teach" calc new transitivity theorems by adding new instances of the Trans type class.

Type classes are introduced later, but the following small example demonstrates how to extend the
calc notation using new Trans instances.
-/

section secret
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..


/-
The example above also makes it clear that you can use calc even if you do not have an infix notation for your relation.

Finally we remark that the vertical bar ∣ in the example above is the unicode one.

We use unicode to make sure we do not overload the ASCII | used in the match .. with expression.

With calc, we can write the proof in the last section in a more natural and perspicuous way.
-/

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]

/-
The alternative calc notation is worth considering here.

When the first expression is taking this much space, using _ in the first relation naturally
aligns all relations:
-/
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]

/-
Here the left arrow before Nat.add_assoc tells rewrite to use the identity in the opposite direction.
(You can enter it with \l or use the ascii equivalent, <-.)

If brevity is what we are after, both rw and simp can do the job on their own:
-/
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc] --rw applies add_mul multiple times, and uses both ways for add_assoc
