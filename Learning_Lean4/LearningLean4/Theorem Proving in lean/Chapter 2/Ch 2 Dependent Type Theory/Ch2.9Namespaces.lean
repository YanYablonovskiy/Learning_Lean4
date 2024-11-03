--Lean provides you with the ability to group definitions into nested, hierarchical namespaces:

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def fa_2 : Nat → Nat := f 
  def fa_3 (f : Nat → Nat): Nat → Nat := f
  def ffa : Nat := f (f a)
  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
#check fa_3 f
#check fa_3 f a
#print f
#print ffa

def l.{u} (a : Type u): Type u := a

/-
When you declare that you are working in the namespace Foo, every identifier 
you declare has a full name with prefix "Foo.". 
Within the namespace, you can refer to identifiers by their shorter names, 
but once you end the namespace, you have to use the longer names. 
Unlike section, namespaces require a name. There is only one anonymous namespace at the root level.

The open command brings the shorter names into the current context.
Often, when you import a module, you will want to open one or more of the namespaces it contains,
to have access to the short identifiers. 
But sometimes you will want to leave this information protected by a fully qualified name, 
for example, when they conflict with identifiers in another namespace you want to use. 
Thus namespaces give you a way to manage names in your working environment.

For example, Lean groups definitions and theorems involving lists into a namespace List.
-/

#check List.nil --⊢ {α : Type u} → List α ; List.nil.{u} {α : Type u} : List α
#check List.cons
#check List.map -- element-wise mapping based on some function α → β ; List.map.{u, v} {α : Type u} {β : Type v} (f : α → β) : List α → List β
#print List.nil
#print List.cons
#print List.map

--The command open List allows you to use the shorter names:


open List -- cant close once opened?

#check nil
#check cons
#check map

--Namespaces that have been closed can later be reopened, even in another file:


namespace Foo_2
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo_2

#check Foo.a
#check Foo.f

namespace Foo_2
  def ffa : Nat := f (f a)
end Foo_2
/-
Like sections, nested namespaces have to be closed in the order they are opened. 
Namespaces and sections serve different purposes: 
namespaces organize data and sections declare variables for insertion in definitions. 
Sections are also useful for delimiting the scope of commands such as set_option and open.
-/

/-
In many respects, however, a namespace ... end block behaves the same as a section ... end block. 
In particular, if you use the variable command within a namespace, its scope is limited to the namespace. 
Similarly, if you use an open command within a namespace, its effects disappear when the namespace is closed.
-/
