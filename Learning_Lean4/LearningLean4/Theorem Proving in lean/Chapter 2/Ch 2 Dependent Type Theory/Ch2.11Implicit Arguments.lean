--Suppose we have an implementation of lists as:


universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs

--definining some TPIL , doesnt seem to exist anymore. The Type parameter is explicit on purpose.

#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α

--Then, you can construct lists of Nat as follows:


#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
#check bs
#print bs

/-
Because the constructors are polymorphic over types, we have to insert the type Nat as an argument repeatedly.
But this information is redundant: one can infer the argument α in Lst.cons Nat 5 (Lst.nil Nat)
from the fact that the second argument, 5, has type Nat.

One can similarly infer the argument in Lst.nil Nat, not from anything else in that expression,
but from the fact that it is sent as an argument to the function Lst.cons,
which expects an element of type Lst α in that position.

This is a central feature of dependent type theory: terms carry a lot of information,
and often some of that information can be inferred from the context.
In Lean, one uses an underscore, _,
to specify that the system should fill in the information automatically.
This is known as an "implicit argument."
-/
#check Lst.cons _ 0 (Lst.nil _)

def as_ : Lst Nat := Lst.nil _
def bs_ : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs

def f ( α : Type ) (a : α) ( β : α → Nat): Nat := β a
def g_1: Nat → Nat := fun a : Nat => a

def k (x: Nat): Nat  := f _ x g_1

#check f _ 5 g_1
#check k

/-
It is still tedious, however, to type all these underscores.
When a function takes an argument that can generally be inferred from context,
Lean allows you to specify that this argument should, by default, be left implicit.
This is done by putting the arguments in curly braces, as follows:
-/



def Lst_a.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst_a.nil {α : Type u} : Lst α := List.nil
def Lst_a.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst_a.cons 0 Lst_a.nil

def as_a: Lst Nat := Lst_a.nil
def bs_a : Lst Nat := Lst_a.cons 5 Lst_a.nil

#check Lst_a.append as_a bs_a


def f_a { α : Type } (a : α) ( β : α → Nat): Nat := β a
def g_2: Nat → Nat := fun a : Nat => a

def k_ (x: Nat): Nat  := f_a x g_2

/-
All that has changed are the braces around α : Type u in the declaration of the variables.
We can also use this device in function definitions:
-/

def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m (not true, maybe out dated -- it is ident.{u} {α : Type u} (x : α) : α)
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α vs ident.{u} {α : Type u} (x : α) : α

/-
This makes the first argument to ident implicit.
Notationally, this hides the specification of the type, making it look as though
ident simply takes an argument of any type.
In fact, the function id is defined in the standard library in exactly this way.
We have chosen a nontraditional name here only to avoid a clash of names.

Variables can also be specified as implicit when they are declared with the variable command:
-/



section
  variable {α : Type u}
  variable (x : α)
  def ident_1 := x
  -- lean knows this x refers to α , and α refers to Type u, and u refers to universe u.
end


#check ident_1
#check ident_1 4
#check ident_1 "hello"

/-
This definition of ident here has the same effect as the one above.

Lean has very complex mechanisms for instantiating implicit arguments,
and we will see that they can be used to infer function types, predicates, and even proofs.

The process of instantiating these "holes," or "placeholders," in a term is often known as elaboration.

The presence of implicit arguments means that at times there may be insufficient information
to fix the meaning of an expression precisely. An expression like id or List.nil is said to be polymorphic,
because it can take on different meanings in different contexts.
-/

/-
One can always specify the type T of an expression e by writing (e : T).
This instructs Lean's elaborator to use the value T as the type of e when trying to resolve implicit arguments.
In the second pair of examples below, this mechanism is used to
specify the desired types of the expressions id and List.nil:
-/

#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat


--(this automatically checks the output is Nat, checks what this implies for the function type)

/-

Numerals are overloaded in Lean, but when the type of a numeral cannot be inferred, Lean assumes,
by default, that it is a natural number.

So the expressions in the first two #check commands below are elaborated in the same way,
whereas the third #check command interprets 2 as an integer.

-/

#check @2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int

#check @id        -- {α : Sort u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool

/-
Notice that now the first #check command gives the type of the identifier, id,
without inserting any placeholders.

Moreover, the output indicates that the first argument is implicit.
-/
