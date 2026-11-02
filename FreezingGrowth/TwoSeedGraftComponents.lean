module

public import FreezingGrowth.TwoSeedGraftGeometry

/-! The graft graph is the union of the master's two actual first-edge
components after the explicit birth-label embedding. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

private theorem graph_map_sup (f : ℕ → ℕ) (G H : SimpleGraph ℕ) :
    (G ⊔ H).map f = G.map f ⊔ H.map f := by
  ext a b
  simp only [SimpleGraph.map_adj', SimpleGraph.sup_adj]
  aesop

private theorem graph_map_edge (f : ℕ → ℕ) (u v : ℕ) :
    (SimpleGraph.edge u v).map f = SimpleGraph.edge (f u) (f v) := by
  ext a b
  simp only [SimpleGraph.map_adj', SimpleGraph.edge_adj]
  aesop

private theorem graph_map_bot (f : ℕ → ℕ) : (⊥ : SimpleGraph ℕ).map f = ⊥ := by
  ext a b
  simp only [SimpleGraph.map_adj', SimpleGraph.bot_adj]
  aesop

theorem parts_replay_wellFormed (p : ℕ → ℕ) (n : ℕ)
    (hp : ∀ j, 2 ≤ j → j ≤ n + 1 → p j < j) :
    RRTSplit.WellFormed n (RRTSplit.replay p n) := by
  induction n with
  | zero => exact RRTSplit.initial_wellFormed
  | succ n ih =>
    exact (ih (fun j hj hj' => hp j hj (by omega))).grow (hp (n + 2) (by omega) le_rfl)

theorem graftEdges_eq_components (T u v : ℕ) (p : ℕ → ℕ) (n : ℕ)
    (hp : ∀ j, 2 ≤ j → j ≤ n + 1 → p j < j) :
    graftEdges T u v p n =
      (RRTSplit.replay p n).rootSide.mappedGraph.map (embedding T u v) ⊔
        (RRTSplit.replay p n).childSide.mappedGraph.map (embedding T u v) := by
  induction n with
  | zero =>
    simp only [graftEdges, RRTSplit.replay, RRTSplit.initial, RRTSplit.Component.initial,
      RRTSplit.Component.mappedGraph, Forward.initial, graph_map_bot, sup_bot_eq]
  | succ n ih =>
    let P := RRTSplit.replay p n
    have hp' : ∀ j, 2 ≤ j → j ≤ n + 1 → p j < j := fun j hj hj' => hp j hj (by omega)
    have hformed : RRTSplit.WellFormed n P := parts_replay_wellFormed p n hp'
    have hn : p (n + 2) < n + 2 := hp (n + 2) (by omega) le_rfl
    have hi : graftEdges T u v p n = P.rootSide.mappedGraph.map (embedding T u v) ⊔
        P.childSide.mappedGraph.map (embedding T u v) := ih hp'
    change graftEdges T u v p n ⊔ SimpleGraph.edge (embedding T u v (p (n + 2))) (T + n + 1) =
      (RRTSplit.grow P (n + 2) (p (n + 2))).rootSide.mappedGraph.map (embedding T u v) ⊔
        (RRTSplit.grow P (n + 2) (p (n + 2))).childSide.mappedGraph.map (embedding T u v)
    rw [hi]
    by_cases hr : p (n + 2) ∈ P.rootSide.labels
    · rw [RRTSplit.grow, ite_eq_left hr]
      simp only
      rw [hformed.root.mappedGraph_attach (n + 2) hr, graph_map_sup, graph_map_edge]
      simp only [embedding]
      ac_rfl
    · have hc := (hformed.mem_or hn).resolve_left hr
      rw [RRTSplit.grow, ite_eq_right hr]
      simp only
      rw [hformed.child.mappedGraph_attach (n + 2) hc, graph_map_sup, graph_map_edge]
      simp only [embedding]
      ac_rfl

/-- Every old edge remains, and the master's first edge is precisely the one
omitted from the union of embedded component graphs. -/
theorem replay_graph_split (s r : Forward.State) (T u v n : ℕ)
    (hv : Forward.ValidAt (n + 1) r)
    (hr : RRTSplit.Describes n r (RRTSplit.split n r)) :
    (replay s T u v r.parent n).graph = s.graph ⊔
      ((RRTSplit.split n r).rootSide.mappedGraph.map (embedding T u v) ⊔
        (RRTSplit.split n r).childSide.mappedGraph.map (embedding T u v)) := by
  have hp : ∀ j, 2 ≤ j → j ≤ n + 1 → r.parent j < j := by
    intro j hj hj'
    apply hv.parent_lt j _ (by omega)
    rw [hr.vertices]
    exact Finset.mem_range.mpr (by omega)
  rw [replay_graph, graftEdges_eq_components T u v r.parent n hp]
  rfl

end FreezingGrowth.TwoSeedGraft
