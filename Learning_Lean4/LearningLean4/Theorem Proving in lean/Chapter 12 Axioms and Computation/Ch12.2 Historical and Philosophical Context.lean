
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Defs
/-
Historical and Philosophical Context:

For most of its history, mathematics was essentially computational:
geometry dealt with constructions of geometric objects, algebra was
concerned with algorithmic solutions to systems of equations, and
analysis provided means to compute the future behavior of systems
evolving over time.

From the proof of a theorem to the effect that "for every x, there
is a y such that ...", it was generally straightforward to extract
an algorithm to compute such a y given x.
-/

/-
In the nineteenth century, however, increases in the complexity of
mathematical arguments pushed mathematicians to develop new styles of
reasoning that suppress algorithmic information and invoke descriptions
of mathematical objects that abstract away the details of how those
objects are represented.

The goal was to obtain a powerful "conceptual" understanding without
getting bogged down in computational details, but this had the effect
of admitting mathematical theorems that are simply false on a direct
computational reading.
-/

/-
For example, consider the following theorem:

Theorem: There exists an irrational number x such that x^x is rational.

A constructive proof would provide a specific irrational number x and
an algorithm to compute x^x, showing that it is rational. However,
a non-constructive proof might simply show that such an x exists
without providing a way to find it.

In Lean, we can state this theorem as follows:
-/


#check Real.cauchy_ratCast
#check Rat.cast
#check RatCast ℝ
#check Membership


variable (y:ℝ) (m: ℕ) (q: ℚ)

#check Real.cauchy_ratCast q



-- theorem exists_irrational_x_rational_x_pow_x : ∃ x : ℝ, (( RatCast x : ℚ)  ∧ (x*x : ℚ)) :=
-- by
--   /-
--   A constructive proof would go here, but this theorem is typically
--   proved non-constructively.
--   -/
--   admit


/-
There is still fairly uniform agreement today that computation is
important to mathematics.

But there are different views as to how best to address computational
concerns.

From a constructive point of view, it is a mistake to separate mathematics
from its computational roots; every meaningful mathematical theorem should
have a direct computational interpretation.

From a classical point of view, it is more fruitful to maintain a
separation of concerns: we can use one language and body of methods to
write computer programs, while maintaining the freedom to use
nonconstructive theories and methods to reason about them.

Lean is designed to support both of these approaches.

Core parts of the library are developed constructively,
but the system also provides support for carrying out
classical mathematical reasoning.
-/

-- Here is an example of a non-constructive proof of the theorem:
-- <theorem exists_irrational_x_rational_x_pow_x : ∃ x : ℝ, ¬(x ∈ ℚ) ∧ (x ^ x ∈ ℚ) :=
-- by
--   use Real.sqrt 2
--   split
--   · intro h
--     have : (Real.sqrt 2) ^ 2 = 2 := Real.mul_self_sqrt (by norm_num)
--     rw [←Rat.cast_coe_nat 2, ←h, Rat.cast_pow, Rat.cast_coe_nat] at this
--     have : (2 : ℚ) = (2 : ℚ) ^ 2 := by rw [this, Rat.cast_pow, Rat.cast_coe_nat]
--     norm_num at this
--   · have : (Real.sqrt 2) ^ (Real.sqrt 2) = Real.sqrt 2 ^ 2 := by sorry
--     rw [this]
--     exact Rat.cast_coe_nat 2>

/-
Computationally, the purest part of dependent type theory avoids the use of
Prop entirely.

Inductive types and dependent function types can be viewed as data types,
and terms of these types can be "evaluated" by applying reduction rules
until no more rules can be applied.

In principle, any closed term (that is, term with no free variables) of
type Nat should evaluate to a numeral, <succ (... (succ zero)...)>.

-/

/-
Introducing a proof-irrelevant Prop and marking theorems irreducible represents
a first step towards separation of concerns.

The intention is that elements of a type p : Prop should play no role
in computation, and so the particular construction of a term t : p is
"irrelevant" in that sense. One can still define computational objects
that incorporate elements of type Prop; the point is that these elements
can help us reason about the effects of the computation, but can be ignored
when we extract "code" from the term.

Elements of type Prop are not entirely innocuous, however.

They include equations s = t : α for any type α, and such equations can
be used as casts, to type check terms.

Below, we will see examples of how such casts can block computation
in the system.

However, computation is still possible under an evaluation scheme that
erases propositional content, ignores intermediate typing constraints,
and reduces terms until they reach a normal form.

This is precisely what Lean's virtual machine does.
-/


/-
Having adopted a proof-irrelevant Prop, one might consider it legitimate
to use, for example, the law of the excluded middle, p ∨ ¬p,
where p is any proposition. Of course, this, too, can block computation
according to the rules of CIC, but it does not block bytecode evaluation,
as described above. It is only the choice principles discussed in :numref:choice
that completely erase the distinction between the proof-irrelevant and
data-relevant parts of the theory.
-/
