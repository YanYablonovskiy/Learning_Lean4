-- Recall that the def keyword provides one important way of declaring new named objects.


def double (x : Nat) : Nat :=
  x + x

#eval double 59999999999

def Zro (x : Nat): Nat :=
x - x

#eval double (Zro 3)

-- This might look more familiar to you if you know how functions work in other programming languages.
-- The name double is defined as a function that takes an input parameter x of type Nat,
-- where the result of the call is x + x, so it is returning type Nat.
-- You can then invoke this function using:


#eval double 3    -- 6


-- In this case you can think of def as a kind of named lambda.
-- The following yields the same result for tripled:


def triple : Nat → Nat :=
  fun x => double x + x

#eval triple 3    -- 6

def double_1 :=
  fun (x : Nat) => x + x -- without the : Nat, does not work. Needs a type to define the dependent arrow type?

  -- The general form of a definition is def foo : α := bar where α is the type returned
  -- from the expression bar. Lean can usually infer the type α,
  -- but it is often a good idea to write it explicitly.
  --  This clarifies your intention, and Lean will flag an error
  --   if the right-hand side of the definition does not have a matching type.

def pi := 3.141592654

-- The right hand side bar can be any expression, not just a lambda.
-- So def can also be used to simply name a value like this:

def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
#eval double 3 = add 3 3 -- True


--The parameter list can be separated like this:


def add_2 (x : Nat) (y : Nat) :=
  x + y

#eval add_2 (double 3) (7 + 9)  -- 22

-- Notice here we called the double function to create the first parameter to add.

-- You can use other more interesting expressions inside a def:
-- You can probably guess what this one will do.

def greater (x y : Nat) :=
  if x > y then x
  else y

#eval greater 1 2
#eval greater 2 1
#eval greater 2 1 = greater 1 2 -- true

-- You can also define a function that takes another function as input.
-- The following calls a given function twice passing the output of the first invocation
-- to the second:


def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8

-- Now to get a bit more abstract, you can also specify arguments that are like type parameters:


def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

-- The type of g and f isnt clear, since they are implicitly defined. This is an example of a dependent
-- arrow?

-- This means compose is a function that takes any two functions as input arguments, so long as those
-- functions each take only one input. The type algebra β → γ and α → β means
-- it is a requirement that the type of the output of the second function
-- must match the type of the input to the first function - which makes sense,
-- otherwise the two functions would not be composable.

-- compose also takes a 3rd argument of type α which it uses to invoke the second function (locally named f) and it passes the result of that function (which is type β) as input to the first function (locally named g). The first function returns a type γ so that is also the return type of the compose function.

--compose is also very general in that it works over any type α β γ. This means compose can compose just about any 2 functions so long as they each take one parameter, and so long as the type of output of the second matches the input of the first. For example:

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
#check compose
