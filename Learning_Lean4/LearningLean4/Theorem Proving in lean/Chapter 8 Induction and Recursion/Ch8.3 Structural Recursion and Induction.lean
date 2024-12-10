/-
Structural Recursion and Induction:

What makes the equation compiler powerful is that it also supports
recursive definitions.

In the next three sections, we will describe, respectively:

- structurally recursive definitions
- well-founded recursive definitions
- mutually recursive definitions

-/

/-
Generally speaking, the equation compiler processes
input of the following form:
-/

/-
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
-/

/-
Here (a : α) is a sequence of parameters, (b : β) is the sequence of
arguments on which pattern matching takes place, and γ is any type,
which can depend on a and b.

Each line should contain the same number of patterns,
one for each element of β.

As we have seen, a pattern is either a variable, a constructor
applied to other patterns, or an expression that normalizes to
something of that form
(where the non-constructors are marked with the [match_pattern] attribute).

The appearances of constructors prompt case splits, with the arguments to
the constructors represented by the given variables.

In Section Dependent Pattern Matching, we will see that it
is sometimes necessary to include explicit terms in patterns that
are needed to make an expression type check, though they do not play a role in
pattern matching.

These are called "inaccessible patterns" for that reason.

But we will not need to use such inaccessible patterns before
Section Dependent Pattern Matching.
-/

def sub2: Nat → Nat
| 0   => Nat.zero
| 1   => 0
| j + 2 => j

def sub2' (n: Nat): Nat :=
match n with
| 0 => 0
| 1 => 0
| j+2 => j

/-
As we saw in the last section, the terms t₁, ..., tₙ can make use of any of the parameters a,
as well as any of the variables that are introduced in the corresponding patterns.

What makes recursion and induction possible is that they can also involve recursive calls to foo.

In this section, we will deal with structural recursion, in which the arguments to foo
occurring on the right-hand side of the => are subterms of the patterns on the left-hand side.

The idea is that they are structurally smaller, and hence appear in the inductive type at an earlier stage.

Here are some examples of structural recursion from the last chapter, now defined using the equation compiler:
-/
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n) -- add m 0 covered by above

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n) --covered case for n being zero, otherwise its succ m and recurses

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n -- mul n 0 covered by above

/-
The proof of zero_add makes it clear that proof by induction is really a form of recursion in Lean.

The example above shows that the defining equations for add hold definitionally, and the same is true of mul.

The equation compiler tries to ensure that this holds whenever possible, as is the case with straightforward
structural induction.

In other situations, however, reductions hold only propositionally, which is to say,
they are equational theorems that must be applied explicitly.

The equation compiler generates such theorems internally.

They are not meant to be used directly by the user; rather, the simp tactic is configured to use
them when necessary.

Thus both of the following proofs of zero_add work:
-/

open Nat
theorem zero_add' : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]

/-
As with definition by pattern matching, parameters to a structural recursion or induction may appear
before the colon.

Such parameters are simply added to the local context before the definition is processed.

For example, the definition of addition may also be written as follows:
-/

open Nat
def add' (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)


/-
You can also write the example above using match.
-/

def add'' (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

/-
A more interesting example of structural recursion is given by the Fibonacci function fib.
-/


def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl


/-
Here, the value of the fib function at n + 2 (which is definitionally equal to succ (succ n))
is defined in terms of the values at n + 1 (which is definitionally equivalent to succ n) and the value at n.

This is a notoriously inefficient way of computing the Fibonacci function, however, with an execution time
that is exponential in n.

Here is a better way:
-/
def fibFast (n : Nat) : Nat :=
  (loop n).2 --keeping the last two values, presenting the latest one (.2)
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1) --first two fib numbers
    | n+1 => let p := loop n; (p.2, p.1 + p.2) -- defining in terms of previous values,
                                               -- here p.2 is the previous value, now second last one
                                               -- and latest value becomes the previous two
#eval fibFast 100

--can do the same without where

def fibFast' (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2


  /-
  In both cases, Lean generates the auxiliary function fibFast.loop.
  -/

  /-
  To handle structural recursion, the equation compiler uses course-of-values recursion,
  using constants below and brecOn that are automatically generated with each inductively defined type.

  You can get a sense of how it works by looking at the types of Nat.below and Nat.brecOn:
  -/

  --brecOn , bottom recurse on?


variable (C : Nat → Type u)

#check @Nat.below --@Nat.below : {motive : Nat → Sort u_1} → Nat → Sort (max 1 u_1)

#check (@Nat.below C : Nat → Type u) --Nat.below : Nat → Type u; given a below motive, returns it?

#reduce @Nat.below C (3 : Nat) --the statement Nat.below 3

#check @Nat.brecOn

--@Nat.brecOn : {motive : Nat → Sort u_1} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
--given a motive, and that its true for a below t, then we have t

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)

--Nat.brecOn : (t : Nat) → ((t : Nat) → Nat.below t → C t) → C t

/-
The type @Nat.below C (3 : nat) is a data structure that stores elements of C 0, C 1, and C 2.

The course-of-values recursion is implemented by Nat.brecOn.

It enables us to define the value of a dependent function of type (n : Nat) → C n at a particular input
n in terms of all the previous values of the function, presented as an element of @Nat.below C n.


The use of course-of-values recursion is one of the techniques the equation compiler uses to justify to the
Lean kernel that a function terminates.

It does not affect the code generator which compiles recursive functions as other
functional programming language compilers.

Recall that #eval fib <n> is exponential on <n>.


-/
def fib' : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n
/-
On the other hand, #reduce fib <n>
is efficient because it uses the definition sent to the kernel that is based on the brecOn construction.
-/
--#eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib

/-
Another good example of a recursive definition is the list append function.
-/
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl

/-
Here is another:
it adds elements of the first list to elements of the second list, until one of the two lists runs out.
-/
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]

/-
You are encouraged to experiment with similar examples in the exercises below.
-/
