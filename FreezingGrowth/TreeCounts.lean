module

public import FreezingGrowth.FiniteLaw

/-! The genuine finite tree has one edge per attachment, including at extinction. -/

@[expose] public section

namespace FreezingGrowth.Forward

open MeasureTheory

theorem ValidAt.edge_count_add_one {n : ℕ} {s : State} (hs : ValidAt n s) :
    Nat.card s.tree.edgeSet + 1 = s.vertices.card := by
  have h := (SimpleGraph.isTree_iff_connected_and_card.mp hs.isTree).2
  have hc : Nat.card {v // v ∈ s.vertices} = s.vertices.card := by simp
  simpa only [hc] using h

/-- The number of edges is the number of attachment operations actually read. -/
theorem treeLaw_edge_count (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, Nat.card s.tree.edgeSet = plusCount x n := by
  filter_upwards [treeLaw_valid x n, treeLaw_counts x n hτ] with s hs hc
  have he := hs.edge_count_add_one
  omega

/-- Only attachments can increase the height, each by at most one.
The bound remains true after absorption, without a survival hypothesis. -/
theorem treeLaw_height_le_plusCount (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, treeHeight s ≤ plusCount x n := by
  have h := treeLaw_ae_induction x
    (fun n s => ValidAt n s ∧ treeHeight s ≤ plusCount x n)
    (by exact ⟨initial_valid, by simp [treeHeight_initial]⟩)
    (by
      intro k s hs _
      refine ⟨hs.1.mono (Nat.le_succ k), ?_⟩
      rw [plusCount_succ]
      split <;> omega)
    (by
      intro k s hs v hv
      refine ⟨hs.1.step _ _, ?_⟩
      rw [Forward.step, ite_eq_left hv, plusCount_succ]
      cases hx : x (k + 1)
      · simpa [treeHeight_freeze] using hs.2
      · simpa only [↓reduceIte] using
          (treeHeight_attach_le_succ hs.1 hv).trans (Nat.add_le_add_right hs.2 1)) n
  exact h.mono (fun _ hs => hs.2)

theorem heightLaw_height_le_plusCount (x : SignSequence) (n : ℕ) :
    ∀ᵐ h ∂heightLaw x n, h ≤ plusCount x n := by
  exact (ae_map_iff measurable_from_top.aemeasurable
    ((Set.to_countable _).measurableSet)).mpr (treeLaw_height_le_plusCount x n)

end FreezingGrowth.Forward

namespace FreezingGrowth.Word

/-- Every word in the paper's family constructs an actual `n`-edge tree. -/
theorem family_edge_count {n : ℕ} {xs : Word} (h : InFamily n xs) :
    ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, Nat.card s.tree.edgeSet = n := by
  have hc := Forward.treeLaw_edge_count xs.toSigns xs.length
    ((admissible_iff_le_extinctionTime xs).mp h.1)
  simpa only [show plusCount xs.toSigns xs.length = n from h.2] using hc

/-- Height is supported on the finite interval from zero to the edge count. -/
theorem family_height_le {n : ℕ} {xs : Word} (h : InFamily n xs) :
    ∀ᵐ k ∂xs.heightLaw, k ≤ n := by
  have hb := Forward.heightLaw_height_le_plusCount xs.toSigns xs.length
  simpa only [heightLaw, show plusCount xs.toSigns xs.length = n from h.2] using hb

end FreezingGrowth.Word
