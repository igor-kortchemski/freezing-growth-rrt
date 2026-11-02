module

public import FreezingGrowth.RRTSplitState
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The actual graph and depths of the first-edge components

Mapped local graphs use the increasing original birth labels. Their union,
plus the first edge, is the actual full graph. The right local root has its
depth reset to zero, and every right depth has global offset one.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open scoped Classical

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

private theorem graph_map_congr {G : SimpleGraph ℕ} {s : Finset ℕ}
    (hG : ∀ {i j}, G.Adj i j → i ∈ s ∧ j ∈ s) {f g : ℕ → ℕ}
    (hfg : ∀ i ∈ s, f i = g i) : G.map f = G.map g := by
  ext a b
  simp only [SimpleGraph.map_adj']
  constructor <;> rintro ⟨hne, i, j, hij, hi, hj⟩
  · exact ⟨hne, i, j, hij, (hfg i (hG hij).1).symm.trans hi,
      (hfg j (hG hij).2).symm.trans hj⟩
  · exact ⟨hne, i, j, hij, (hfg i (hG hij).1).trans hi,
      (hfg j (hG hij).2).trans hj⟩

namespace Component

def mappedGraph (c : Component) : SimpleGraph ℕ := c.tree.graph.map c.label

theorem label_mem (c : Component) {i : ℕ} (hi : i < c.labels.length) :
    c.label i ∈ c.labels := by
  simp only [label, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem WellFormed.mappedGraph_adj_mem {r : ℕ} {c : Component} (hc : WellFormed r c)
    {u v : ℕ} (h : c.mappedGraph.Adj u v) : u ∈ c.labels ∧ v ∈ c.labels := by
  obtain ⟨_, i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
  obtain ⟨hi, hj⟩ := hc.valid.adj_mem hij
  rw [hc.vertices] at hi hj
  exact ⟨c.label_mem (Finset.mem_range.mp hi), c.label_mem (Finset.mem_range.mp hj)⟩

/-- Appending a birth preserves every old mapped edge and adds exactly the
actual edge from its original parent to its original birth identifier. -/
theorem WellFormed.mappedGraph_attach {r : ℕ} {c : Component} (hc : WellFormed r c)
    (t : ℕ) {v : ℕ} (hv : v ∈ c.labels) :
    (c.attach t v).mappedGraph = c.mappedGraph ⊔ SimpleGraph.edge v t := by
  change (c.tree.graph ⊔ SimpleGraph.edge (c.labels.idxOf v) c.labels.length).map
      (c.attach t v).label = _
  rw [graph_map_sup, graph_map_edge]
  have hgraph : c.tree.graph.map (c.attach t v).label = c.mappedGraph := by
    apply graph_map_congr hc.valid.adj_mem
    intro i hi
    rw [hc.vertices] at hi
    exact label_attach_old c t v i (Finset.mem_range.mp hi)
  rw [hgraph, label_attach_new, label_attach_old _ _ _ _
    (List.idxOf_lt_length_of_mem hv), label_idxOf hv]

end Component

/-- Full graph/depth correspondence, in addition to the complete local-state
invariants. This is stronger than identifying the two height distributions. -/
structure Describes (n : ℕ) (s : Forward.State) (p : Parts) : Prop where
  formed : WellFormed n p
  vertices : s.vertices = Finset.range (n + 2)
  active : s.active = Finset.range (n + 2)
  graph : s.graph = p.rootSide.mappedGraph ⊔ p.childSide.mappedGraph ⊔ SimpleGraph.edge 0 1
  root_height : ∀ i, i < p.rootSide.labels.length →
    s.height (p.rootSide.label i) = p.rootSide.tree.height i
  child_height : ∀ i, i < p.childSide.labels.length →
    s.height (p.childSide.label i) = p.childSide.tree.height i + 1

theorem initial_describes : Describes 0 (Forward.attach Forward.initial 1 0) initial := by
  refine ⟨initial_wellFormed, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Forward.attach, Forward.initial, Finset.range_add_one]
  · simp [Forward.attach, Forward.initial, Finset.range_add_one]
  · simp [Forward.attach, Forward.initial, initial, Component.initial, Component.mappedGraph,
      graph_map_bot]
  · intro i hi
    have hi0 : i = 0 := by simpa [initial, Component.initial] using hi
    subst i
    simp [Forward.attach, Forward.initial, initial, Component.initial, Component.label]
  · intro i hi
    have hi0 : i = 0 := by simpa [initial, Component.initial] using hi
    subst i
    simp [Forward.attach, Forward.initial, initial, Component.initial, Component.label]

/-- The full correspondence is preserved by each genuine uniform-parent
attachment, independently of its probability. -/
theorem Describes.attach {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) {v : ℕ} (hv : v < n + 2) :
    Describes (n + 1) (Forward.attach s (n + 2) v) (grow p (n + 2) v) := by
  have hf := hs.formed.grow hv
  have hverts : (Forward.attach s (n + 2) v).vertices = Finset.range (n + 1 + 2) := by
    simp only [Forward.attach, hs.vertices]
    ext u
    simp only [Finset.mem_insert, Finset.mem_range]
    omega
  have hact : (Forward.attach s (n + 2) v).active = Finset.range (n + 1 + 2) := by
    simp only [Forward.attach, hs.active]
    ext u
    simp only [Finset.mem_insert, Finset.mem_range]
    omega
  by_cases hr : v ∈ p.rootSide.labels
  · have hgr : grow p (n + 2) v = ⟨p.rootSide.attach (n + 2) v, p.childSide⟩ := by
      rw [grow, ite_eq_left hr]
    rw [hgr] at hf ⊢
    refine ⟨hf, hverts, hact, ?_, ?_, ?_⟩
    · change s.graph ⊔ SimpleGraph.edge v (n + 2) = _
      rw [hs.graph, hs.formed.root.mappedGraph_attach _ hr]
      ac_rfl
    · intro i hi
      by_cases hiold : i < p.rootSide.labels.length
      · have hli : p.rootSide.label i < n + 2 :=
          hs.formed.root_lt _ (p.rootSide.label_mem hiold)
        change Function.update s.height (n + 2) (s.height v + 1)
            ((p.rootSide.attach (n + 2) v).label i) =
          Function.update p.rootSide.tree.height p.rootSide.labels.length
            (p.rootSide.tree.height (p.rootSide.labels.idxOf v) + 1) i
        rw [Component.label_attach_old _ _ _ _ hiold,
          Function.update_of_ne (ne_of_lt hli), Function.update_of_ne (ne_of_lt hiold)]
        exact hs.root_height i hiold
      · have hi' : i = p.rootSide.labels.length := by
          simp only [Component.attach, List.length_append, List.length_singleton] at hi
          omega
        subst i
        change Function.update s.height (n + 2) (s.height v + 1)
            ((p.rootSide.attach (n + 2) v).label p.rootSide.labels.length) =
          Function.update p.rootSide.tree.height p.rootSide.labels.length
            (p.rootSide.tree.height (p.rootSide.labels.idxOf v) + 1) p.rootSide.labels.length
        rw [Component.label_attach_new, Function.update_self, Function.update_self]
        have h := hs.root_height _ (List.idxOf_lt_length_of_mem hr)
        rw [Component.label_idxOf hr] at h
        exact congrArg (fun z => z + 1) h
    · intro i hi
      have hli : p.childSide.label i < n + 2 :=
        hs.formed.child_lt _ (p.childSide.label_mem hi)
      change Function.update s.height (n + 2) (s.height v + 1) (p.childSide.label i) = _
      rw [Function.update_of_ne (ne_of_lt hli)]
      exact hs.child_height i hi
  · have hc := (hs.formed.mem_or hv).resolve_left hr
    have hgr : grow p (n + 2) v = ⟨p.rootSide, p.childSide.attach (n + 2) v⟩ := by
      rw [grow, ite_eq_right hr]
    rw [hgr] at hf ⊢
    refine ⟨hf, hverts, hact, ?_, ?_, ?_⟩
    · change s.graph ⊔ SimpleGraph.edge v (n + 2) = _
      rw [hs.graph, hs.formed.child.mappedGraph_attach _ hc]
      ac_rfl
    · intro i hi
      have hli : p.rootSide.label i < n + 2 :=
        hs.formed.root_lt _ (p.rootSide.label_mem hi)
      change Function.update s.height (n + 2) (s.height v + 1) (p.rootSide.label i) = _
      rw [Function.update_of_ne (ne_of_lt hli)]
      exact hs.root_height i hi
    · intro i hi
      by_cases hiold : i < p.childSide.labels.length
      · have hli : p.childSide.label i < n + 2 :=
          hs.formed.child_lt _ (p.childSide.label_mem hiold)
        change Function.update s.height (n + 2) (s.height v + 1)
            ((p.childSide.attach (n + 2) v).label i) =
          Function.update p.childSide.tree.height p.childSide.labels.length
            (p.childSide.tree.height (p.childSide.labels.idxOf v) + 1) i + 1
        rw [Component.label_attach_old _ _ _ _ hiold,
          Function.update_of_ne (ne_of_lt hli), Function.update_of_ne (ne_of_lt hiold)]
        exact hs.child_height i hiold
      · have hi' : i = p.childSide.labels.length := by
          simp only [Component.attach, List.length_append, List.length_singleton] at hi
          omega
        subst i
        change Function.update s.height (n + 2) (s.height v + 1)
            ((p.childSide.attach (n + 2) v).label p.childSide.labels.length) =
          Function.update p.childSide.tree.height p.childSide.labels.length
            (p.childSide.tree.height (p.childSide.labels.idxOf v) + 1) p.childSide.labels.length + 1
        rw [Component.label_attach_new, Function.update_self, Function.update_self]
        have h := hs.child_height _ (List.idxOf_lt_length_of_mem hc)
        rw [Component.label_idxOf hc] at h
        omega

end FreezingGrowth.RRTSplit
