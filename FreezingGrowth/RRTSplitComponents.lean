module

public import FreezingGrowth.RRTSplitSupport
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Graph isomorphisms for the two genuine first-edge components

Removing the actual edge with birth identifiers 0 and 1 leaves the disjoint
union of the two mapped local trees. The local labels enumerate each component
in increasing birth order. The local states retain the usual root and outside
vertex defaults, not only an unlabelled shape or a height statistic.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open scoped Classical

namespace Component

theorem WellFormed.mappedGraph_adj_iff {r : ℕ} {c : Component} (hc : WellFormed r c)
    {i j : ℕ} (hi : i ∈ c.tree.vertices) (hj : j ∈ c.tree.vertices) :
    c.mappedGraph.Adj (c.label i) (c.label j) ↔ c.tree.graph.Adj i j := by
  constructor
  · rintro ⟨_, a, b, hab, ha, hb⟩
    obtain ⟨haV, hbV⟩ := hc.valid.adj_mem hab
    have hai : a = i := hc.label_injective (hc.vertices ▸ haV) (hc.vertices ▸ hi) ha
    have hbj : b = j := hc.label_injective (hc.vertices ▸ hbV) (hc.vertices ▸ hj) hb
    simpa only [hai, hbj] using hab
  · intro hij
    refine ⟨?_, i, j, hij, rfl, rfl⟩
    intro he
    exact hij.ne (hc.label_injective (hc.vertices ▸ hi) (hc.vertices ▸ hj) he)

/-- Birth-order relabeling is a bijection of the actual finite vertex sets. -/
noncomputable def labelEquiv {r : ℕ} {c : Component} (hc : WellFormed r c) :
    {i // i ∈ c.tree.vertices} ≃ {v // v ∈ c.labels.toFinset} :=
  Equiv.ofBijective
    (fun i => ⟨c.label i.val, List.mem_toFinset.mpr (c.label_mem
      (Finset.mem_range.mp (hc.vertices ▸ i.property)))⟩)
    ⟨by
      intro i j he
      apply Subtype.ext
      exact hc.label_injective (hc.vertices ▸ i.property) (hc.vertices ▸ j.property)
        (congrArg Subtype.val he), by
      intro v
      have hv : v.val ∈ c.labels := List.mem_toFinset.mp v.property
      refine ⟨⟨c.labels.idxOf v.val, ?_⟩, ?_⟩
      · rw [hc.vertices]
        exact Finset.mem_range.mpr (List.idxOf_lt_length_of_mem hv)
      · apply Subtype.ext
        exact label_idxOf hv⟩

@[simp] theorem labelEquiv_val {r : ℕ} {c : Component} (hc : WellFormed r c)
    (i : {i // i ∈ c.tree.vertices}) : (labelEquiv hc i).val = c.label i.val := rfl

theorem labelEquiv_root {r : ℕ} {c : Component} (hc : WellFormed r c) :
    (labelEquiv hc ⟨0, hc.valid.root_mem⟩).val = r := hc.label_zero

/-- Full graph isomorphism, using the same explicit increasing labels. -/
noncomputable def mappedTreeIso {r : ℕ} {c : Component} (hc : WellFormed r c) :
    c.tree.tree ≃g c.mappedGraph.induce (c.labels.toFinset : Set ℕ) where
  toEquiv := labelEquiv hc
  map_rel_iff' := by
    intro i j
    exact hc.mappedGraph_adj_iff i.property j.property

end Component

/-- No mapped local component contains the first edge. -/
theorem Describes.no_first_edge {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) :
    ¬p.rootSide.mappedGraph.Adj 0 1 ∧ ¬p.childSide.mappedGraph.Adj 0 1 := by
  have hr : 0 ∈ p.rootSide.labels := by
    obtain ⟨tail, h⟩ := hs.formed.root.rooted
    simp [h]
  have hc : 1 ∈ p.childSide.labels := by
    obtain ⟨tail, h⟩ := hs.formed.child.rooted
    simp [h]
  constructor
  · intro he
    exact hs.formed.disjoint (hs.formed.root.mappedGraph_adj_mem he).2 hc
  · intro he
    exact hs.formed.disjoint hr (hs.formed.child.mappedGraph_adj_mem he).1

private theorem delete_first_edge_eq_self {G : SimpleGraph ℕ} (h : ¬G.Adj 0 1) :
    G.deleteEdges {s(0, 1)} = G := by
  ext u v
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · exact And.left
  · intro huv
    refine ⟨huv, ?_⟩
    intro he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h huv
    · exact h huv.symm

/-- Literal deletion of the first edge leaves exactly these two mapped trees. -/
theorem Describes.delete_first_edge {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) :
    s.graph.deleteEdges {s(0, 1)} = p.rootSide.mappedGraph ⊔ p.childSide.mappedGraph := by
  rw [hs.graph, SimpleGraph.deleteEdges_sup, SimpleGraph.deleteEdges_sup,
    delete_first_edge_eq_self hs.no_first_edge.1,
    delete_first_edge_eq_self hs.no_first_edge.2]
  simp

/-- The first canonical local tree is the actual root-side component after
edge deletion, with the explicit birth-order vertex bijection. -/
noncomputable def Describes.rootComponentIso {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) :
    p.rootSide.tree.tree ≃g
      (s.graph.deleteEdges {s(0, 1)}).induce (p.rootSide.labels.toFinset : Set ℕ) where
  toEquiv := Component.labelEquiv hs.formed.root
  map_rel_iff' := by
    intro i j
    change (s.graph.deleteEdges {s(0, 1)}).Adj (p.rootSide.label i.val)
      (p.rootSide.label j.val) ↔ p.rootSide.tree.graph.Adj i.val j.val
    rw [hs.delete_first_edge, SimpleGraph.sup_adj]
    constructor
    · rintro (h | h)
      · exact hs.formed.root.mappedGraph_adj_iff i.property j.property |>.mp h
      · exact False.elim (hs.formed.disjoint
          (p.rootSide.label_mem (Finset.mem_range.mp (hs.formed.root.vertices ▸ i.property)))
          (hs.formed.child.mappedGraph_adj_mem h).1)
    · intro h
      exact Or.inl (hs.formed.root.mappedGraph_adj_iff i.property j.property |>.mpr h)

/-- The second canonical local tree is the component rooted at birth1; its
local root has depth zero and corresponds to that actual endpoint. -/
noncomputable def Describes.childComponentIso {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) :
    p.childSide.tree.tree ≃g
      (s.graph.deleteEdges {s(0, 1)}).induce (p.childSide.labels.toFinset : Set ℕ) where
  toEquiv := Component.labelEquiv hs.formed.child
  map_rel_iff' := by
    intro i j
    change (s.graph.deleteEdges {s(0, 1)}).Adj (p.childSide.label i.val)
      (p.childSide.label j.val) ↔ p.childSide.tree.graph.Adj i.val j.val
    rw [hs.delete_first_edge, SimpleGraph.sup_adj]
    constructor
    · rintro (h | h)
      · exact False.elim (hs.formed.disjoint
          (hs.formed.root.mappedGraph_adj_mem h).1
          (p.childSide.label_mem (Finset.mem_range.mp (hs.formed.child.vertices ▸ i.property))))
      · exact hs.formed.child.mappedGraph_adj_iff i.property j.property |>.mp h
    · intro h
      exact Or.inr (hs.formed.child.mappedGraph_adj_iff i.property j.property |>.mpr h)

end FreezingGrowth.RRTSplit
