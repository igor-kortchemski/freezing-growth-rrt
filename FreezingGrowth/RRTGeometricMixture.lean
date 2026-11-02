module

public import FreezingGrowth.RRTSplitCDF
public import FreezingGrowth.HeightMonotonicity
public import Mathlib.Probability.Distributions.Geometric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Moments.Basic

/-!
# The geometric mixture of actual recursive-tree heights

The geometric index counts edges, starting at zero. No identification with
an infinite branching process is assumed in this module.
-/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable def geometricParameter (t : ℝ≥0) : unitInterval :=
  ⟨Real.exp (-(t : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.coe_nonneg)⟩

@[simp] theorem geometricParameter_coe (t : ℝ≥0) :
    (geometricParameter t : ℝ) = Real.exp (-(t : ℝ)) := rfl

theorem geometricParameter_ne_zero (t : ℝ≥0) : geometricParameter t ≠ 0 := by
  intro h
  have := congrArg (fun p : unitInterval => (p : ℝ)) h
  change Real.exp (-(t : ℝ)) = 0 at this
  exact Real.exp_ne_zero (-(t : ℝ)) this

noncomputable def geometricIndexLaw (t : ℝ≥0) : Measure ℕ :=
  geometricMeasure (geometricParameter t)

instance geometricIndexLaw_isProbabilityMeasure (t : ℝ≥0) :
    IsProbabilityMeasure (geometricIndexLaw t) := by
  unfold geometricIndexLaw
  infer_instance

noncomputable def geometricHeightLaw (t : ℝ≥0) : Measure ℕ :=
  (geometricIndexLaw t).bind (fun n => Forward.heightLaw allAttach n)

instance geometricHeightLaw_isProbabilityMeasure (t : ℝ≥0) :
    IsProbabilityMeasure (geometricHeightLaw t) :=
  isProbabilityMeasure_bind measurable_from_top.aemeasurable
    (Filter.Eventually.of_forall (fun _ => inferInstance))

theorem geometricIndexLaw_singleton (t : ℝ≥0) (n : ℕ) :
    (geometricIndexLaw t).real {n} =
      (1 - Real.exp (-(t : ℝ))) ^ n * Real.exp (-(t : ℝ)) :=
  geometricMeasure_real_singleton (geometricParameter_ne_zero t) n

@[simp] theorem geometricIndexLaw_zero : geometricIndexLaw 0 = Measure.dirac 0 := by
  ext E hE
  rw [geometricIndexLaw, geometricMeasure_eq (geometricParameter_ne_zero 0),
    Measure.sum_apply _ hE]
  simp only [geometricParameter, NNReal.coe_zero, neg_zero, Real.exp_zero,
    sub_self, mul_one, Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

@[simp] theorem geometricHeightLaw_zero : geometricHeightLaw 0 = Measure.dirac 0 := by
  rw [geometricHeightLaw, geometricIndexLaw_zero, Measure.dirac_bind measurable_from_top]
  simp [Forward.heightLaw, Forward.treeLaw, Measure.map_dirac' measurable_from_top,
    Forward.treeHeight_initial]

theorem geometricHeightLaw_real_eq_integral (t : ℝ≥0) (E : Set ℕ) :
    (geometricHeightLaw t).real E =
      ∫ n, (Forward.heightLaw allAttach n).real E ∂geometricIndexLaw t := by
  unfold Measure.real geometricHeightLaw
  rw [Measure.bind_apply E.to_countable.measurableSet measurable_from_top.aemeasurable]
  exact (integral_toReal measurable_from_top.aemeasurable
    (Filter.Eventually.of_forall (fun n => measure_lt_top _ _))).symm

/-- Every event has the expected absolutely convergent mixture series. -/
theorem geometricHeightLaw_real_series (t : ℝ≥0) (E : Set ℕ) :
    (geometricHeightLaw t).real E = ∑' n : ℕ,
      (1 - Real.exp (-(t : ℝ))) ^ n * Real.exp (-(t : ℝ)) *
        (Forward.heightLaw allAttach n).real E := by
  rw [geometricHeightLaw_real_eq_integral, geometricIndexLaw,
    integral_geometricMeasure (geometricParameter_ne_zero t)]
  rfl

theorem geometricHeightLaw_event_integrable (t : ℝ≥0) (E : Set ℕ) :
    Integrable (fun n => (Forward.heightLaw allAttach n).real E)
      (geometricIndexLaw t) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    measurable_from_top.aestronglyMeasurable
  filter_upwards [] with n
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

theorem geometricHeightLaw_event_summable (t : ℝ≥0) (E : Set ℕ) :
    Summable (fun n : ℕ =>
      (1 - Real.exp (-(t : ℝ))) ^ n * Real.exp (-(t : ℝ)) *
        (Forward.heightLaw allAttach n).real E) := by
  simpa only [geometricParameter_coe, smul_eq_mul] using
    (hasSum_integral_geometricMeasure (geometricParameter_ne_zero t)
      (geometricHeightLaw_event_integrable t E)).summable

/-- Only the zero-edge tree has height zero. -/
theorem geometricHeightLaw_cdf_zero (t : ℝ≥0) :
    (geometricHeightLaw t).real {h | h ≤ 0} = Real.exp (-(t : ℝ)) := by
  rw [geometricHeightLaw_real_series]
  rw [tsum_eq_single 0]
  · simp only [pow_zero, one_mul, RRTSplit.heightLaw_cdf_initial, mul_one]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp only [RRTSplit.heightLaw_cdf_zero, mul_zero]

/-- Exact geometric index tail, including the degenerate time-zero case. -/
theorem geometricIndexLaw_tail (t : ℝ≥0) (n : ℕ) :
    (geometricIndexLaw t).real {k | n < k} =
      (1 - Real.exp (-(t : ℝ))) ^ (n + 1) := by
  have hc : {k : ℕ | n < k} = (↑(Finset.range (n + 1)) : Set ℕ)ᶜ := by
    ext k
    simp
  rw [hc, measureReal_compl (Finset.measurableSet _), probReal_univ,
    ← sum_measureReal_singleton]
  simp_rw [geometricIndexLaw_singleton]
  rw [← Finset.sum_mul]
  have hg := geom_sum_mul_neg (1 - Real.exp (-(t : ℝ))) (n + 1)
  simp only [sub_sub_cancel] at hg
  linarith

private theorem geometric_ratio_norm_lt_one (t : ℝ≥0) :
    ‖1 - Real.exp (-(t : ℝ))‖ < 1 := by
  have hu : Real.exp (-(t : ℝ)) ≤ 1 := (geometricParameter t).2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu)]
  linarith [Real.exp_pos (-(t : ℝ))]

theorem geometricIndexLaw_integrable (t : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (geometricIndexLaw t) := by
  rw [geometricIndexLaw, integrable_geometricMeasure_iff (geometricParameter_ne_zero t)]
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (geometric_ratio_norm_lt_one t)).summable.mul_right (Real.exp (-(t : ℝ)))
  convert h using 1
  ext n
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n), geometricParameter_coe]
  ring

/-- Mean number of edges, not number of vertices. -/
theorem geometricIndexLaw_mean (t : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂geometricIndexLaw t) = Real.exp (t : ℝ) - 1 := by
  rw [geometricIndexLaw, integral_geometricMeasure (geometricParameter_ne_zero t)]
  simp only [geometricParameter_coe, smul_eq_mul]
  have he : ∀ n : ℕ,
      (1 - Real.exp (-(t : ℝ))) ^ n * Real.exp (-(t : ℝ)) * n =
        (n * (1 - Real.exp (-(t : ℝ))) ^ n) * Real.exp (-(t : ℝ)) := by
    intro n
    ring
  simp_rw [he]
  rw [tsum_mul_right, tsum_coe_mul_geometric_of_norm_lt_one
    (geometric_ratio_norm_lt_one t)]
  have hx : Real.exp (t : ℝ) ≠ 0 := Real.exp_ne_zero _
  rw [Real.exp_neg]
  field_simp
  ring

theorem geometricIndexLaw_tail_le_mean (t : ℝ≥0) (n : ℕ) :
    (geometricIndexLaw t).real {k | n < k} ≤
      (Real.exp (t : ℝ) - 1) / ((n : ℝ) + 1) := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := geometricIndexLaw t) (f := fun k : ℕ => (k : ℝ))
    (Filter.Eventually.of_forall (fun k => Nat.cast_nonneg k))
    (geometricIndexLaw_integrable t) ((n : ℝ) + 1)
  have he : {k : ℕ | (n : ℝ) + 1 ≤ (k : ℝ)} = {k : ℕ | n < k} := by
    ext k
    simp only [Set.mem_ofPred_eq]
    exact_mod_cast Nat.succ_le_iff
  rw [he, geometricIndexLaw_mean] at h
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    (by simpa [mul_comm] using h)

/-- Mixing over a random size loses at most the probability of exceeding `n`.
No independence between the sampled height and its index is asserted. -/
theorem geometricHeightLaw_tail_le (t : ℝ≥0) (n d : ℕ) :
    (geometricHeightLaw t).real {h | d ≤ h} ≤
      (Forward.heightLaw allAttach n).real {h | d ≤ h} +
        (geometricIndexLaw t).real {k | n < k} := by
  let a := (Forward.heightLaw allAttach n).real {h | d ≤ h}
  have hI : Integrable (Set.indicator {k : ℕ | n < k} (fun _ => (1 : ℝ)))
      (geometricIndexLaw t) :=
    (integrable_const 1).indicator (Set.to_countable _).measurableSet
  rw [geometricHeightLaw_real_eq_integral]
  calc
    _ ≤ ∫ k : ℕ, a + Set.indicator {k : ℕ | n < k} (fun _ => (1 : ℝ)) k
        ∂geometricIndexLaw t := by
      apply integral_mono (geometricHeightLaw_event_integrable t _)
        ((integrable_const a).add hI)
      intro k
      change (Forward.heightLaw allAttach k).real {h | d ≤ h} ≤
        a + Set.indicator {k : ℕ | n < k} (fun _ => (1 : ℝ)) k
      by_cases hk : k ≤ n
      · simp only [Set.indicator_of_notMem (show k ∉ {k : ℕ | n < k} by simpa using hk),
          add_zero]
        exact Forward.heightLaw_real_tail_mono_time allAttach hk d
      · rw [Set.indicator_of_mem (show k ∈ {k : ℕ | n < k} by simpa using hk)]
        have hnon : 0 ≤ a := measureReal_nonneg
        have hb : (Forward.heightLaw allAttach k).real {h | d ≤ h} ≤ 1 := measureReal_le_one
        linarith
    _ = _ := by
      rw [integral_add (integrable_const a) hI, integral_const,
        integral_indicator_const 1 (Set.to_countable _).measurableSet]
      simp [a]

end FreezingGrowth.RRT
