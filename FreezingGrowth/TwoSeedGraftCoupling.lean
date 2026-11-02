module

public import FreezingGrowth.TwoSeedGraftSample
public import FreezingGrowth.TwoSeedGraftComponents
public import FreezingGrowth.TwoSeedGraftHistory

/-! Actual full-state marginals and support of the common master graft. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory
open scoped Classical

theorem active_eq_pair_of_card_two {s : Forward.State} (hc : s.active.card = 2)
    {p : ℕ × ℕ} (hp : p ∈ s.active.offDiag) : s.active = {p.1, p.2} := by
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  have hsub : ({p.1, p.2} : Finset ℕ) ⊆ s.active := by
    intro a ha'
    rcases Finset.mem_insert.mp ha' with rfl | ha'
    · exact ha
    · rcases Finset.mem_singleton.mp ha' with rfl
      exact hb
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, Finset.card_pair hab])).symm

def Parameters (T n : ℕ) (z : Sample) : Prop :=
  Forward.ValidAt T z.initial ∧ z.initial.active = {z.first, z.second} ∧ z.first ≠ z.second ∧
    Forward.ValidAt (n + 1) z.master ∧ RRTSplit.Describes n z.master (RRTSplit.split n z.master)

theorem stateSampleLaw_ae_parameters (s : Forward.State) {T : ℕ} (hs : Forward.ValidAt T s)
    (hc : s.active.card = 2) (n : ℕ) : ∀ᵐ z ∂stateSampleLaw s n, Parameters T n z := by
  rw [ae_iff, stateSampleLaw, Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
  apply (lintegral_eq_zero_iff (measurable_of_countable _)).mpr
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag s.active] with p hp
  apply ae_iff.mp
  apply (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mpr
  filter_upwards [Forward.treeLaw_valid RRT.allAttach (n + 1), RRTSplit.treeLaw_split_describes n]
    with r hr hparts
  exact ⟨hs, active_eq_pair_of_card_two hc hp, (Finset.mem_offDiag.mp hp).2.2, hr, hparts⟩

theorem sampleLaw_ae_parameters (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    ∀ᵐ z ∂sampleLaw xs n, Parameters xs.length n z := by
  rw [ae_iff, sampleLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  apply (lintegral_eq_zero_iff measurable_from_top).mpr
  filter_upwards [Forward.treeLaw_valid xs.toSigns xs.length, hc] with s hs hc
  exact ae_iff.mp (stateSampleLaw_ae_parameters s hs hc n)

theorem stateSampleLaw_baseline (s : Forward.State) {T : ℕ} (hs : Forward.ValidAt T s)
    (hc : s.active.card = 2) (n : ℕ) :
    (stateSampleLaw s n).map (baselineState T n) = continuationLaw s T n := by
  let := uniformRootPair_isProbabilityMeasure s.active (by omega : 2 ≤ s.active.card)
  rw [stateSampleLaw, Measure.map_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  calc
    _ = (uniformRootPair s.active).bind (fun _ => continuationLaw s T n) := by
      apply Measure.bind_congr_right
      filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag s.active] with p hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      rw [Measure.map_map measurable_from_top measurable_from_top]
      exact masterTree_replay_law s (hs.vertices_le _ (hs.active_subset ha))
        (hs.vertices_le _ (hs.active_subset hb)) hab (active_eq_pair_of_card_two hc hp) n
    _ = _ := by rw [Measure.bind_const, measure_univ, one_smul]

theorem sampleLaw_baseline (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (sampleLaw xs n).map (baselineState xs.length n) =
      Forward.treeLaw (xs ++ List.replicate n true).toSigns (xs ++ List.replicate n true).length := by
  rw [sampleLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    word_bind_continuation]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid xs.toSigns xs.length, hc] with s hs hc
  exact stateSampleLaw_baseline s hs hc n

/-- Both graft components and the old complete frozen tree remain present on
the actual sample, with the original global birth-label interleaving. -/
theorem sampleLaw_baseline_graph (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    ∀ᵐ z ∂sampleLaw xs n,
      (baselineState xs.length n z).graph = z.initial.graph ⊔
        ((RRTSplit.split n z.master).rootSide.mappedGraph.map (embedding xs.length z.first z.second) ⊔
          (RRTSplit.split n z.master).childSide.mappedGraph.map (embedding xs.length z.first z.second)) := by
  filter_upwards [sampleLaw_ae_parameters xs n hc] with z hz
  exact replay_graph_split z.initial z.master xs.length z.first z.second n hz.2.2.2.1 hz.2.2.2.2

end FreezingGrowth.TwoSeedGraft
