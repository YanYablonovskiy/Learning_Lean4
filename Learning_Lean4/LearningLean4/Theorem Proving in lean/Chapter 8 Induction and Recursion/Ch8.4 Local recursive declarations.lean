/-
Local recursive declarations
You can define local recursive declarations using the let rec keyword.
-/

def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α --Loop has Nat and List arguments
    | 0,   as => as --eq compiler on nat only, when 0 case returns second argument
    | n+1, as => loop n (a::as) --when not 0, n+1, runs loop on n and appending a to the list
  loop n [] --end result, n length list of element a

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α

#eval replicate (n:=3) (a := 3) --[3, 3, 3]
#eval replicate 4 5 --[5, 5, 5, 5]

/-
Lean creates an auxiliary declaration for each let rec.

In the example above, it created the declaration replicate.loop for the let
rec loop occurring at replicate.

Note that, Lean "closes" the declaration by adding any local variable occurring in the let
rec declaration as additional parameters.

For example, the local variable a occurs at let rec loop.

You can also use let rec in tactic mode and for creating proofs by induction.
-/

open Nat

#check @Nat.add_comm
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n];simp_arith;admit

/-
You can also introduce auxiliary recursive declarations using where clause after your definition.

Lean converts them into a let rec.
-/

def replicate' (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate' (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n];simp_arith
