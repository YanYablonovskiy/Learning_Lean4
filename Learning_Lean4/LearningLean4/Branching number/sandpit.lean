import Mathlib.Combinatorics.SimpleGraph.path

section

  universe u
  variable {V : Type u} (G : SimpleGraph V)

  /-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
  def IsAcyclic : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle


--   structure Tree (T : Type u ) extends SimpleGraph K where
--      Prop: ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle
-- end
