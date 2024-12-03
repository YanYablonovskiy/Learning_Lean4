/-
In Lean, identifiers are given by hierarchical names like Foo.Bar.baz.

We saw in Namespaces that Lean provides mechanisms for working with hierarchical names.

The command namespace foo causes foo to be prepended to the name of each definition and
theorem until end foo is encountered.

The command open foo then creates temporary aliases to definitions and theorems that begin with prefix foo.
-/
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar
#check Foo.bar

/-
The following definition
-/
def Foo.baz : Nat := 1
/-
is treated as a macro, and expands to
-/
namespace Foo
def baz' : Nat := 1 --' added not to overlap
end Foo

/-
Although the names of theorems and definitions have to be unique, the aliases that identify them do not.


--meaning different namespaces can have the same named function; default is _root_

When we open a namespace, an identifier may be ambiguous.

Lean tries to use type information to disambiguate the meaning in context,
but you can always disambiguate by giving the full name.

To that end, the string _root_ is an explicit description of the empty prefix.
-/


--example of the same name; and inferring the alias by type

def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- ambiguous
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type

/-
We can prevent the shorter alias from being created by using the protected keyword:
-/
protected def Foo.bza : Nat := 1

open Foo

--#check bza -- error
#check Foo.bza

/-
This is often used for names like Nat.rec and Nat.recOn, to prevent overloading of common names.

The open command admits variations. The command
-/
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3

/-
creates aliases for only the identifiers listed. The command
-/
open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3

/-
creates aliases for everything in the Nat namespace except the identifiers listed.
-/
section
--open Nat renaming mul → times, add → plus
-- get error ambiguous namespace 'Nat', possible interpretations: '[Nat, Nat.Nat]'
--#eval plus (times 2 2) 3  -- 7
end
/-
creates aliases renaming Nat.mul to times and Nat.add to plus.

It is sometimes useful to export aliases from one namespace to another, or to the top level. The command
-/
export Nat (succ add sub)

/-
creates aliases for succ, add, and sub in the current namespace, so that whenever the namespace is open,
these aliases are available.

If this command is used outside a namespace, the aliases are exported to the top level.
-/
