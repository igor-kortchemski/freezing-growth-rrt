module

public import FreezingGrowth.PWIT.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Lattice

/-!
# The finite cyclic-minimum argument

The weighted identity below is a generic integration lemma. Its hypotheses
explicitly require rotations of the full probability space, invariance of the
weight, and absence of ties. Applying it to a sampled rank-class path still
requires proving those hypotheses for the actual joint path law.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped BigOperators Classical

def minimumAt {ι : Type*} (b : ι → ℝ) (r : ι) : Prop := ∀ j, b r ≤ b j

theorem existsUnique_minimumAt {ι : Type*} [Finite ι] [Nonempty ι]
    {b : ι → ℝ} (hb : Function.Injective b) : ∃! r, minimumAt b r := by
  obtain ⟨r, hr⟩ := Finite.exists_min b
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact hb (le_antisymm (hs r) (hr s))

def bridgeRotate {d : ℕ} [NeZero d] (r : Fin d) (b : Fin d → ℝ) : Fin d → ℝ :=
  fun j => b (r + j) - b r

theorem minimumAt_bridgeRotate_zero {d : ℕ} [NeZero d] (r : Fin d) (b : Fin d → ℝ) :
    minimumAt (bridgeRotate r b) 0 ↔ minimumAt b r := by
  simp only [minimumAt, bridgeRotate, add_zero, sub_self, sub_nonneg]
  constructor
  · intro h j
    simpa using h (j - r)
  · intro h j
    exact h (r + j)

theorem measurableSet_minimumAt {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {b : Ω → ι → ℝ} (hb : Measurable b) (r : ι) :
    MeasurableSet {ω | minimumAt (b ω) r} := by
  unfold minimumAt
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le ((measurable_pi_apply r).comp hb) ((measurable_pi_apply j).comp hb)

theorem sum_minimum_indicator {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (hb : Function.Injective b) (w : ℝ) :
    (∑ r, if minimumAt b r then w else 0) = w := by
  classical
  obtain ⟨r, hr, hu⟩ := existsUnique_minimumAt hb
  rw [Finset.sum_eq_single r]
  · simp [hr]
  · intro s _ hsr
    have hs : ¬minimumAt b s := fun hs => hsr (hu s hs)
    simp [hs]
  · simp

/-- Division-free weighted cyclic identity. The transformations act on the
entire sample, so their invariance includes any endpoint used by the weight.
This lemma does not postulate exchangeability of a fixed rank word. -/
theorem integral_weighted_cyclic_minimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} [NeZero d]
    (b : Ω → Fin d → ℝ) (w : Ω → ℝ) (T : Fin d → Ω → Ω)
    (hb : Measurable b) (hw : Integrable w μ)
    (hT : ∀ r, MeasurePreserving (T r) μ μ)
    (hweight : ∀ r, ∀ᵐ ω ∂μ, w (T r ω) = w ω)
    (hbridge : ∀ r, ∀ᵐ ω ∂μ, b (T r ω) = bridgeRotate r (b ω))
    (hdistinct : ∀ᵐ ω ∂μ, Function.Injective (b ω)) :
    (d : ℝ) * (∫ ω, {ω | minimumAt (b ω) 0}.indicator w ω ∂μ) = ∫ ω, w ω ∂μ := by
  classical
  have hi (r : Fin d) : Integrable ({ω | minimumAt (b ω) r}.indicator w) μ :=
    hw.indicator (measurableSet_minimumAt hb r)
  have he (r : Fin d) :
      (∫ ω, {ω | minimumAt (b ω) r}.indicator w ω ∂μ) =
        ∫ ω, {ω | minimumAt (b ω) 0}.indicator w ω ∂μ := by
    calc
      _ = ∫ ω, {ω | minimumAt (b ω) 0}.indicator w (T r ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hweight r, hbridge r] with ω hw' hb'
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, hb',
          minimumAt_bridgeRotate_zero, hw']
      _ = _ := by
        have hm := integral_map (hT r).measurable.aemeasurable
          (show AEStronglyMeasurable ({ω | minimumAt (b ω) 0}.indicator w)
            (μ.map (T r)) from (hT r).map_eq.symm ▸ (hi 0).aestronglyMeasurable)
        rw [(hT r).map_eq] at hm
        exact hm.symm
  calc
    _ = ∑ r : Fin d, ∫ ω, {ω | minimumAt (b ω) r}.indicator w ω ∂μ := by
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∫ ω, ∑ r : Fin d, {ω | minimumAt (b ω) r}.indicator w ω ∂μ := by
      rw [integral_finsetSum _ fun r _ => hi r]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hdistinct] with ω hω
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
        sum_minimum_indicator (b ω) hω (w ω)

end FreezingGrowth.PWIT
