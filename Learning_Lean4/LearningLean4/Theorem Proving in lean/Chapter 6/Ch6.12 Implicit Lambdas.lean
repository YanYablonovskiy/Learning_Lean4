/-Implicit Lambdas

In Lean 3 stdlib, we find many instances of the dreadful @+_ idiom. 

It is often used when the expected type is a function type with implicit arguments, 
and we have a constant (reader_t.pure in the example) which also takes implicit arguments. 

In Lean 4, the elaborator automatically introduces lambdas for consuming implicit arguments. 

We are still exploring this feature and analyzing its impact, 
but the experience so far has been very positive. 

Here is the example from the link above using Lean 4 implicit lambdas.

-/
variable  {ρ : Type u}
variable  {m : Type u → Type v}
variable  [Monad m]
variable {α β : Type u}


instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind

/-
Users can disable the implicit lambda feature by using @ or writing a lambda 
expression with {} or [] binder annotations. 

Here are few examples
-/
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
