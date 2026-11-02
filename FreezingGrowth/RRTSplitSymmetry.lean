module

public import FreezingGrowth.RRTSplitLaw
import Mathlib.Algebra.BigOperators.Intervals

/-! Exchangeability after forgetting the first-edge component size tag. -/

@[expose] public section
namespace FreezingGrowth.RRTSplit

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

noncomputable def pairLaw (n : ℕ) : Measure (Forward.State × Forward.State) :=
  (Forward.treeLaw RRT.allAttach (n + 1)).map (fun s => (firstEdgeSplit n s).2)

instance pairLaw_probability (n : ℕ) : IsProbabilityMeasure (pairLaw n) :=
  Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

theorem pairLaw_eq_sum (n : ℕ) :
    pairLaw n = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
      ∑ k ∈ Finset.range (n + 1),
        (Forward.treeLaw RRT.allAttach k).prod (Forward.treeLaw RRT.allAttach (n - k)) := by
  have h := congrArg (Measure.map Prod.snd) (treeLaw_firstEdgeSplit n)
  rw [Measure.map_map measurable_snd measurable_from_top, mixtureLaw_eq_sum,
    Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_finset_sum measurable_snd.aemeasurable] at h
  have hc (k : ℕ) : (componentLaw k (n - k)).map Prod.snd =
      (Forward.treeLaw RRT.allAttach k).prod (Forward.treeLaw RRT.allAttach (n - k)) := by
    rw [componentLaw, Measure.map_map measurable_snd measurable_prodMk_left]
    simp [Function.comp_def]
  simp_rw [hc] at h
  exact h

theorem pairLaw_swap (n : ℕ) : (pairLaw n).map Prod.swap = pairLaw n := by
  rw [pairLaw_eq_sum, Measure.map_smul _ measurable_swap.aemeasurable,
    Measure.map_finset_sum measurable_swap.aemeasurable]
  simp_rw [Measure.prod_swap]
  congr 1
  rw [← Finset.sum_range_reflect (fun k =>
    (Forward.treeLaw RRT.allAttach k).prod (Forward.treeLaw RRT.allAttach (n - k)))
    (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  congr 2
  omega

noncomputable def heightPairLaw (n : ℕ) : Measure (ℕ × ℕ) :=
  (pairLaw n).map (fun p => (Forward.treeHeight p.1, Forward.treeHeight p.2))

theorem measurable_heightPair : Measurable
    (fun p : Forward.State × Forward.State =>
      (Forward.treeHeight p.1, Forward.treeHeight p.2)) := by
  have hh : Measurable Forward.treeHeight := measurable_from_top
  simpa [Function.comp_def] using
    (hh.comp measurable_fst).prodMk (hh.comp measurable_snd)

instance heightPairLaw_probability (n : ℕ) : IsProbabilityMeasure (heightPairLaw n) :=
  Measure.isProbabilityMeasure_map_iff measurable_heightPair.aemeasurable |>.mpr inferInstance

theorem heightPairLaw_swap (n : ℕ) :
    (heightPairLaw n).map Prod.swap = heightPairLaw n := by
  have h := congrArg (Measure.map (fun p : Forward.State × Forward.State =>
    (Forward.treeHeight p.1, Forward.treeHeight p.2))) (pairLaw_swap n)
  rw [Measure.map_map measurable_heightPair measurable_swap] at h
  rw [heightPairLaw, Measure.map_map measurable_swap measurable_heightPair]
  exact h

theorem heightPairLaw_tie_le_half (n : ℕ) :
    (heightPairLaw n).real {p | p.1 = p.2 + 1} ≤ (1 / 2 : ℝ) := by
  let μ := heightPairLaw n
  let E : Set (ℕ × ℕ) := {p | p.1 = p.2 + 1}
  let F : Set (ℕ × ℕ) := {p | p.2 = p.1 + 1}
  have hE : MeasurableSet E := E.to_countable.measurableSet
  have hF : MeasurableSet F := F.to_countable.measurableSet
  have heq : μ.real E = μ.real F := by
    have h := map_measureReal_apply measurable_swap hE (μ := μ)
    rw [heightPairLaw_swap] at h
    exact h
  have hd : Disjoint E F := Set.disjoint_left.mpr (by
    intro p hp hq
    change p.1 = p.2 + 1 at hp
    change p.2 = p.1 + 1 at hq
    omega)
  have hu : μ.real (E ∪ F) ≤ 1 := by
    calc
      μ.real (E ∪ F) ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  rw [measureReal_union hd hF, ← heq] at hu
  change μ.real E ≤ _
  linarith

end FreezingGrowth.RRTSplit
