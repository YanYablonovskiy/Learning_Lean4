/-
Wildcards and Overlapping Patterns

Consider one of the examples from the last section:
-/
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2

-- my version
def foo' : Nat → Nat → Nat
  | 0,   0   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
  | 0, n+1 => 0

/-
An alternative presentation is:
-/
def foo'' : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2

/-
In the second presentation, the patterns overlap; for example, the pair of '
arguments 0 0 matches all three cases. 

But Lean handles the ambiguity by using the first applicable equation, 
so in this example the net result is the same. 

In particular, the following equations hold definitionally:
-/

example : foo 0     0     = 0 := rfl
example : foo 0     (n+1) = 0 := rfl
example : foo (m+1) 0     = 1 := rfl
example : foo (m+1) (n+1) = 2 := rfl

example : foo' 0     0     = 0 := rfl
example : foo' 0     (n+1) = 0 := rfl
example : foo' (m+1) 0     = 1 := rfl
example : foo' (m+1) (n+1) = 2 := rfl

example : foo'' 0     0     = 0 := rfl
example : foo'' 0     (n+1) = 0 := rfl
example : foo'' (m+1) 0     = 1 := rfl
example : foo'' (m+1) (n+1) = 2 := rfl

/-
Since the values of m and n are not needed, 
we can just as well use wildcard patterns instead.
-/

def foo''' : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

/-
You can check that this definition of foo satisfies the same 
definitional identities as before.

Some functional programming languages support incomplete patterns. 
arbitrary value for incomplete cases. 

We can simulate the arbitrary value approach using the Inhabited type class. 

Roughly, an element of Inhabited α is a witness to the fact that there 
is an element of α; in the Chapter Type Classes we will see that Lean 
can be instructed that suitable base types are inhabited, and 
can automatically infer that other constructed types are inhabited. 

On this basis, the standard library provides a default element, 
default, of any inhabited type.
-/

/-
We can also use the type Option α to simulate incomplete patterns. 

The idea is to return some a for the provided patterns, and use none for 
the incomplete cases. 

The following example demonstrates both approaches.
-/

def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl

/-
The equation compiler is clever. 

If you leave out any of the cases in the following definition, 
the error message will let you know what has not been covered.
-/
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0 --covers 2 cases, 6 left
  | 0,   b :: _, _     => b --covers 2 cases, 4 left
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b

--total options are 8, but first one covers 2 cases, second covers 2 also

/-
It will also use an "if ... then ... else" instead of a 
casesOn in appropriate situations.
-/
def foo'''' : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
