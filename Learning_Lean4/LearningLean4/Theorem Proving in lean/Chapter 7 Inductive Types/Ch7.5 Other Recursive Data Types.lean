/-
Other Recursive Data Types
Let us consider some more examples of inductively defined types.

For any type, α, the type List α of lists of elements of α is defined in the library.
-/

namespace Hidden
inductive List (α : Type u) where
  | nil  : List α --either empty list
  | cons : α → List α → List α --or a head element, with a list after it -- head and tail
                               --repeated applications yield either nill or α → (α → List α → List α) → List α
end Hidden

namespace List

def appendₛ (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (appendₛ as bs)

theorem nil_appendₛ (as : List α) : appendₛ nil as = as :=
  rfl

theorem cons_appendₛ (a : α) (as bs : List α)
                    : appendₛ (cons a as) bs = cons a (appendₛ as bs) :=
  rfl

/-
A list of elements of type α is either the empty list, nil, or an element h : α followed by a list t : List α.

The first element, h, is commonly known as the "head" of the list, and the remainder, t,
is known as the "tail."

-/

/-
For another example, we can define the type of binary trees:
-/

/-
In fact, we can even define the type of countably branching trees:
-/
--spherically symmetric, regular tree


end List

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t) -- uses CBTree.sup;

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree
#check succ


end CBTree
