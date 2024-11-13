/-
Negation, ¬p, is actually defined to be p → False, so we obtain ¬p by deriving a contradiction from p.

Similarly, the expression hnp hp produces a proof of False from hp : p and hnp : ¬p.

The next example uses both these rules to produce a proof of (p → q) → ¬q → ¬p.

(The symbol ¬ is produced by typing \not or \neg.)
-/

-- my attempt at (p → q) → ¬q → ¬p.
#check False
variable (p q : Prop)

example (h: p → q) (hnq: ¬q): ¬p :=
--fun (hp:p) => And.intro (h hp) (hnq)
--wrong
--type mismatch
--   ⟨h hp, hnq⟩
-- has type
--   q ∧ ¬q : Prop
-- but is expected to have type
--   False : Prop
fun (hp:p) => hnq (h hp)

-- TPIL version

example (hpq : p → q) (hnq : ¬q) : ¬p := -- (p → q) → ¬ q ( → ¬p)
  fun hp : p =>
  show False from hnq (hpq hp)

--version with false elim
example (hpq : p → q) (hnq : ¬q) : ¬p := -- (p → q) → ¬ q ( → ¬p)
  fun hp : p =>
  False.elim (hnq (hpq hp))


/-
The connective False has a single elimination rule, False.elim, which expresses the fact that anything follows from a contradiction.

This rule is sometimes called ex falso (short for ex falso sequitur quodlibet), or the principle of explosion.

-/

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp) --whereas ¬ is the introduction

#check False.elim
#print False.elim

#check False.rec --false has a recursor
#print False.rec

#check ¬ _

/-
The arbitrary fact, q, that follows from falsity is an implicit argument
in False.elim and is inferred automatically.

This pattern, deriving an arbitrary fact from contradictory hypotheses, is quite common,
and is represented by absurd.
-/
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

#check absurd
#print absurd

--version with absurd
example (hpq : p → q) (hnq : ¬q) : ¬p := -- (p → q) → ¬ q ( → ¬p)
  fun hp : p =>
  absurd (hpq hp) hnq

/-
Here, for example, is a proof of ¬p → q → (q → p) → r:
-/

  --my version

example {r:Prop} (hnp: ¬ p) (hq: q) (hqp: q → p): r:=
False.elim (hnp (hqp hq))

--TPIL

variable (r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

/-
Incidentally, just as False has only an elimination rule, True has only an introduction rule,
True.intro : true.

In other words, True is simply true, and has a canonical proof, True.intro.

-/
