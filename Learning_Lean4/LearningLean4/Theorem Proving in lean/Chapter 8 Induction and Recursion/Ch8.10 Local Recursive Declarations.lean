/-
You can define local recursive declarations using the let rec keyword:

-/
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α --implicit n and a
    | 0,   as => as
    | n+1, as => loop n (a::as) --structural recursion on n, guaranteed to terminate
  loop n [] --start with empty list, kleisli composition

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α

/-
Lean creates an auxiliary declaration for each let rec.

In the example above, it created the declaration replicate.loop for the let
rec loop occurring at replicate.

Note that, Lean "closes" the declaration by adding any local variable occurring
in the let rec declaration as additional parameters.

For example, the local variable a occurs at let rec loop.

You can also use let rec in tactic mode and for creating proofs by induction:
-/


theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n];simp_arith; --induction using n
  exact aux n []

  /-
  You can also introduce auxiliary recursive declarations using a where clause after
  your definition.

  Lean converts them into a let rec:
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
    | n+1 => simp [replicate.loop, aux n];simp_arith;
