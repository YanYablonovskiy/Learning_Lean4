/-
The short explanation is that types can depend on parameters. 
You have already seen a nice example of this: the type List α depends on the argument α, 
and this dependence is what distinguishes List Nat and List Bool.
 For another example, consider the type Vector α n, the type of vectors of elements of α of length n. 
 This type depends on two parameters: the type of the elements in the vector (α : Type) 
 and the length of the vector n : Nat.

Suppose you wish to write a function cons which inserts a new element at the head of a list. 
What type should cons have? Such a function is polymorphic: you expect the cons function for Nat, Bool, 
or an arbitrary type α to behave the same way. 
So it makes sense to take the type to be the first argument to cons, so that for any type, 
α, cons α is the insertion function for lists of type α. 
In other words, for every α, cons α is the function that takes an element a : α and a list as : List α, 
and returns a new list, so you have cons α a as : List α.

It is clear that cons α should have type α → List α → List α. 
But what type should cons have? 
A first guess might be Type → α → List α → List α, 
but, on reflection, this does not make sense: 
the α in this expression does not refer to anything, 
whereas it should refer to the argument of type Type. 
In other words, assuming α : Type is the first argument to the function, 
the type of the next two elements are α and List α. These types vary depending on the first argument, α.
-/
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α

def consu (α : Type u) (a : α) (as : List α) : List α :=
  List.cons a as

#check consu Nat        -- Nat → List Nat → List Nat
#check consu Bool       -- Bool → List Bool → List Bool
#check consu            -- (α : Type u) (a : α) (as : List α) : List α