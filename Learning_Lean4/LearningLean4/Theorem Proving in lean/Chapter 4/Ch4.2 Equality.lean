/-
Let us now turn to one of the most fundamental relations defined in Lean's library, namely, the equality relation.

In Chapter Inductive Types, we will explain how equality is defined from the primitives of Lean's logical framework.

In the meanwhile, here we explain how to use it.

Of course, a fundamental property of equality is that it is an equivalence relation:
-/
#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c

/-
We can make the output easier to read by telling Lean not to insert the implicit arguments
(which are displayed here as metavariables).
-/
universe u

#check @Eq.refl.{u}   -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

def Eq_t {α: Type u} (a:α): Prop := a=a

#check @Eq_t

/-
The inscription .{u} tells Lean to instantiate the constants at the universe u.

Thus, for example, we can specialize the example from the previous section to the equality relation:
-/
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

example : a = d :=
  Eq.trans (Eq.trans  --Eq.trans hab (b=c) is Eq.trans (a=b) (b=c) => a = c
            hab (
                  Eq.symm hcb   --Eq.symm hcb gets b = c
                ))
            hcd --Eq.trans (a=c) (c=d) gets a = d
--my version
example: (α : Type) → (hab : a = b) → (hcb : c = b) →  (hcd : c = d) → (a=d)
:= fun  (α : Type) (hab : a = b) (hcb : c = b) =>
  Eq.trans (Eq.trans hab (Eq.symm hcb))

/-
We can also use the projection notation:
-/
example : a = d := (hab.trans hcb.symm).trans hcd

--hab.trans hcb.symm =  (Eq.trans hab (Eq.symm hcb)) , so => a = c
--(hab.trans hcb.symm).trans hcd = Eq.trans (a=c) hcd = (a=c).trans (c=d) => a = d

/-
Reflexivity is more powerful than it looks.

Recall that terms in the Calculus of Constructions have a computational interpretation,
and that the logical framework treats terms with a common reduct as the same.

As a result, some nontrivial identities can be proved by reflexivity:

-/

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

#check Eq.refl _

--my versions

example: (f : α → β) → (a : α)  → ((fun x => f x) a = f a) :=
fun (hf: α → β) => fun (a: α)  => Eq.refl (hf a)

/-
This feature of the framework is so important that the library defines a notation rfl for Eq.refl _:
-/

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

--my versions:

example: (a : α) → (b : β) → (a , b).1 = a :=
fun (a:α) (b:β) =>  Eq.refl ((a,b).1)

/-
Equality is much more than an equivalence relation, however.

It has the important property that every assertion respects the equivalence,
in the sense that we can substitute equal expressions without changing the truth value.

That is, given h1 : a = b and h2 : p a, we can construct a proof for p b using substitution: Eq.subst h1 h2.
-/
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

--my version

example: (a: α) → (b: α) → (pq: α → Prop) → (hab: a=b) → (p: (pq a)) → (pq b) :=
fun (a b: α) (pq: α → Prop) (hab: a=b)  (p: (pq a)) => Eq.subst hab p


/-
The triangle in the second presentation is a macro built on top of Eq.subst and Eq.symm, and you can enter it by typing \t.

The rule Eq.subst is used to define the following auxiliary rules, which carry out more explicit substitutions.

They are designed to deal with applicative terms, that is, terms of form s t.

Specifically, congrArg can be used to replace the argument, congrFun can be used to replace the term that is being applied,
and congr can be used to replace both at once.
-/

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁ --swap a with b in the goal arguments via h_1
example : f a = g a := congrFun h₂ a --swap f and g in the goal function via h_2
example : f a = g b := congr h₂ h₁ -- in the 'goal' swap functions via h_2 then argument via h_1

/-
Lean's library contains a large number of common identities, such as these:
-/

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

/-
Note that Nat.mul_add and Nat.add_mul are alternative names for Nat.left_distrib and Nat.right_distrib, respectively.

The properties above are stated for the natural numbers (type Nat).

Here is an example of a calculation in the natural numbers that uses substitution combined with associativity and distributivity.
-/
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y -- (x+y) over x + y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1 --sub in (x+y)*y = x*y + y*y in h1
                                                   --then sub in (x+y)x = x*x + y*x to (sub in (x+y)*y = x*y + y*y in h1)
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm --rearrange equality and remove ( )

/-
Notice that the second implicit parameter to Eq.subst, which provides the context in which the substitution is to occur,
has type α → Prop. Inferring this predicate therefore requires an instance of higher-order unification.

In full generality, the problem of determining whether a higher-order unifier exists is undecidable,
and Lean can at best provide imperfect and approximate solutions to the problem. As a result,
Eq.subst doesn't always do what you want it to.

The macro h ▸ e uses more effective heuristics for computing this implicit parameter, and often succeeds in situations where applying Eq.subst fails.

Because equational reasoning is so common and important, Lean provides a number of mechanisms
to carry it out more effectively.

The next section offers syntax that allow you to write calculational proofs in a more natural and perspicuous way.

But, more importantly, equational reasoning is supported by a term rewriter, a simplifier, and other kinds of automation.

The term rewriter and simplifier are described briefly in the next section, and then in greater detail in the next chapter.
-/
