module

public import FreezingGrowth.ReverseConstructionEquivalence
public import FreezingGrowth.FiniteLaw

/-!
# Maximum-height transport between the two constructions

The imported law equivalence is proved for complete canonical states. This
module transports the actual maximum root-distance observable, including
terminal extinction, to the graph-valued reverse construction. It also
forgets freezing timestamps to retain precisely active/frozen labels.

The ordered-list interpretation and the delayed-pair coupling of Algorithm 3
are separate obligations. No deletion domination is assumed or asserted here.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped Classical

namespace RootedForest

/-- Maximum distance from a vertex to its component root. -/
def maxDepth {V : Type*} [DecidableEq V] (F : RootedForest V) : ℕ :=
  F.vertices.sup F.depth

/-- The stored depths are genuine graph distances, including at the maximum. -/
theorem maxDepth_eq_max_distance {V : Type*} [DecidableEq V] (F : RootedForest V) :
    F.maxDepth = F.vertices.sup (fun v => F.graph.dist (F.root v) v) := by
  apply Finset.sup_congr rfl
  intro v hv
  exact F.depth_eq_dist hv

end RootedForest

namespace CanonicalTree

/-- Transport to canonical vertex IDs preserves the actual maximum height. -/
theorem treeHeight_reverseState {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    Forward.treeHeight (reverseState F) = F.forest.maxDepth := by
  change (F.forest.vertices.image F.edgeTime).sup (reverseState F).height = _
  rw [Finset.sup_image]
  apply Finset.sup_congr rfl
  intro v hv
  exact (reverseState_vertex_data hinj hv).2.1

/-- The source's binary-labelled rooted tree observable, on canonical IDs. -/
structure AFTree where
  vertices : Finset ℕ
  graph : SimpleGraph ℕ
  root : ℕ
  active : Finset ℕ

instance : MeasurableSpace AFTree := ⊤

/-- Every vertex outside `active` is frozen; freezing timestamps are forgotten. -/
def eraseFreezingTimes (T : Observable) : AFTree :=
  ⟨T.vertices, T.graph, 0, T.active⟩

/-- The richer construction equivalence implies equality with only the
active/frozen labels displayed in the manuscript. -/
theorem binaryLabelled_construction_laws_eq (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (forwardLaw x n).map eraseFreezingTimes =
      (reverseLaw x n).map eraseFreezingTimes := by
  rw [construction_laws_eq x n hn]

end CanonicalTree

namespace Reverse

/-- Maximum-height law of the genuine graph-valued reverse construction. -/
noncomputable def heightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).map RootedForest.maxDepth

instance heightLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (heightLaw x n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable).mpr inferInstance

end Reverse

namespace Forward

/-- The maximum-height law is preserved by reversal, including the case of
an initially empty reverse forest at terminal extinction. -/
theorem heightLaw_eq_reverseHeightLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    heightLaw x n = Reverse.heightLaw x n := by
  unfold heightLaw
  rw [← CanonicalTree.reverseStateLaw_eq_forward_treeLaw x n hn]
  unfold CanonicalTree.reverseStateLaw
  rw [Measure.map_map measurable_from_top measurable_from_top]
  calc
    _ = (ReverseStamped.treeLaw x n).map (fun F => F.forest.maxDepth) := by
      apply Measure.map_congr
      filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn] with F hF
      exact CanonicalTree.treeHeight_reverseState hF.1
    _ = Reverse.heightLaw x n := by
      unfold Reverse.heightLaw
      rw [← ReverseStamped.map_treeLaw x n,
        Measure.map_map measurable_from_top measurable_from_top]
      rfl

end Forward

namespace Word

/-- Finite choice words need only the manuscript's admissibility condition;
the horizon may equal extinction. -/
theorem heightLaw_eq_reverseHeightLaw (xs : Word) (ha : xs.admissible) :
    xs.heightLaw = Reverse.heightLaw xs.toSigns xs.length :=
  Forward.heightLaw_eq_reverseHeightLaw xs.toSigns xs.length
    ((admissible_iff_le_extinctionTime xs).mp ha)

end Word
end FreezingGrowth
