/-
Named Arguments:

Named arguments enable you to specify an argument for a parameter by matching the argument with its name rather
than with its position in the parameter list.

If you don't remember the order of the parameters but know their names, you can send the arguments in any order.

You may also provide the value for an implicit parameter when Lean failed to infer it.

Named arguments also improve the readability of your code by identifying what each argument represents.
-/

def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁

/-
In the following examples, we illustrate the interaction between named and default arguments.
-/

def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=  --contains default arguments y and w
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl --fixing z

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl --showing can swap order

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl  --default value of y overrriden

example : f = (fun x z => x + 1 + 2 - z) := rfl --using both default arguments

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl --locking in x x → z => ..

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl --changing value of y, using default w

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α := --instance of addition on α
  match b? with
  | none   => a + c --if b has no value
  | some b => a + b + c

variable {α} [Add α] --auto inputs

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl

/-
You can use .. to provide missing explicit arguments as _.

This feature combined with named arguments is useful for writing patterns. Here is an example:
-/

inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none

/-
Ellipses are also useful when explicit arguments can be automatically inferred by Lean,
and we want to avoid a sequence of _s.
-/
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
