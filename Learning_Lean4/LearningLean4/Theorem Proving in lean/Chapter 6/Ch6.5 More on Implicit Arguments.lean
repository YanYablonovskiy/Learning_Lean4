/-
In Section Implicit Arguments, we saw that if Lean displays the type of a term t as {x : α} → β x,
then the curly brackets indicate that x has been marked as an implicit argument to t.

This means that whenever you write t, a placeholder, or "hole," is inserted, so that t is replaced by @t _.

If you don't want that to happen, you have to write @t instead.

-/

/-
Notice that implicit arguments are inserted eagerly.

Suppose we define a function f (x : Nat) {y : Nat} (z : Nat) with the arguments shown.

Then, when we write the expression f 7 without further arguments, it is parsed as f 7 _.

Lean offers a weaker annotation, {{y : Nat}}, which specifies that a placeholder should only be added
before a subsequent explicit argument.

This annotation can also be written using as ⦃y : Nat⦄, where the unicode brackets are entered
as \{{ and \}}, respectively.

With this annotation, the expression f 7 would be parsed as is, whereas f 7 3 would be parsed as f 7 _ 3,
just as it would be with the strong annotation.

To illustrate the difference, consider the following example, which shows that a reflexive euclidean relation
is both symmetric and transitive.
-/

section
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _) --aplying r a b → r a c → r b c, but c = a, so reflr _( a ) gives r a a

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  show r a c from euclr (symmr rab) rbc -- get r a c, from using euclr to get r b a → r b c → r a c


variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check @euclidean
#check euclidean r
#check @(euclidean r)
#check euclr
#check @euclr

--here is what shows the difference
theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr

#check euclr  -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3
end

/-
The results are broken down into small steps: th1 shows that a relation that is reflexive and euclidean is symmetric,
and th2 shows that a relation that is symmetric and euclidean is transitive.

Then th3 combines the two results.

But notice that we have to manually disable the implicit arguments in euclr, because otherwise
too many implicit arguments are inserted.

The problem goes away if we use weak implicit arguments:
-/

section
def reflexive' {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric' {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive' {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean' {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1' {α : Type u} {r : α → α → Prop}
            (reflr : reflexive' r) (euclr : euclidean' r)
            : symmetric' r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2' {α : Type u} {r : α → α → Prop}
            (symmr : symmetric' r) (euclr : euclidean' r)
            : transitive' r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3' {α : Type u} {r : α → α → Prop}
            (reflr : reflexive' r) (euclr : euclidean' r)
            : transitive' r :=
  th2' (th1' reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- euclidean r

end

/-
There is a third kind of implicit argument that is denoted with square brackets, [ and ].

These are used for type classes, as explained in Chapter Type Classes.
-/
