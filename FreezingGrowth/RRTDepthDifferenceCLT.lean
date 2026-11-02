module

public import FreezingGrowth.RRTDepthPairProduct
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The source depth-difference central limit theorem

Two distinct vertices are sampled uniformly from the same recursive tree.
Their signed depth difference, divided by `sqrt(log n)`, converges in law to
the centered Gaussian of variance two. The proof uses the actual attachment
recurrence and a scalar characteristic-function argument.
-/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

/-- All vertices, including the root, participate in the actual distinct sample. -/
theorem distinctDepthDifferenceLaw_eq_bind_vertices {n : ℕ} (hn : 1 ≤ n) :
    distinctDepthDifferenceLaw n = (Forward.treeLaw allAttach n).bind
      (fun s => (uniformRootPair s.vertices).map (signedDepthDifference s)) := by
  unfold distinctDepthDifferenceLaw
  apply Measure.bind_congr_right
  filter_upwards [active_eq_vertices n,
    Forward.treeLaw_counts allAttach n (before_extinction n).le] with s hs hc
  have hcZ : (s.active.card : ℤ) = (n : ℤ) + 1 := by
    simpa only [activeCount_allAttach] using hc.1
  change (if 2 ≤ s.active.card then _ else Measure.dirac 0) = _
  rw [ite_eq_left (by omega : 2 ≤ s.active.card), hs]

noncomputable def distinctDepthDifferenceCosine (n : ℕ) (t : ℝ) : ℝ :=
  ∫ z : ℤ, Real.cos (t * z) ∂distinctDepthDifferenceLaw n

theorem depthDifferenceLaw_integral_sin (n : ℕ) (t : ℝ) :
    (∫ z : ℤ, Real.sin (t * z) ∂depthDifferenceLaw n) = 0 := by
  have h := depthDifferenceLaw_integral_neg n (fun z => Real.sin (t * z))
  simp only [Int.cast_neg, mul_neg, Real.sin_neg, integral_neg] at h
  linarith

theorem distinctDepthDifferenceLaw_integral_sin {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (∫ z : ℤ, Real.sin (t * z) ∂distinctDepthDifferenceLaw n) = 0 := by
  have h := depthDifferenceLaw_integral_distinct hn (fun z => Real.sin (t * z))
  rw [depthDifferenceLaw_integral_sin] at h
  simp only [Int.cast_zero, mul_zero, Real.sin_zero, add_zero] at h
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    have hh : 1 / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  exact (mul_eq_zero.mp h.symm).resolve_left hp.ne'

theorem tendsto_distinctDepthDifferenceCosine_normalized (t : ℝ) :
    Tendsto (fun n => distinctDepthDifferenceCosine n (depthDifferenceFrequency t n))
      atTop (𝓝 (Real.exp (-(t ^ 2)))) := by
  have herr : Tendsto (fun n => depthDifferenceCosine n (depthDifferenceFrequency t n) -
      distinctDepthDifferenceCosine n (depthDifferenceFrequency t n)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    apply squeeze_zero_norm' _ hbound
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact depthDifferenceLaw_distinct_test_error hn
      (fun z => Real.cos (depthDifferenceFrequency t n * z)) (fun _ => Real.abs_cos_le_one _)
  have h := (tendsto_depthDifferenceCosine_normalized t).sub herr
  simpa only [sub_sub_cancel, sub_zero] using h

/-- A probability measure on the real line with the exact source normalization. -/
noncomputable def normalizedDistinctDepthDifferenceLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(distinctDepthDifferenceLaw n).map (fun z : ℤ => (z : ℝ) / Real.sqrt (Real.log n)),
    Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance⟩

theorem charFun_normalizedDistinctDepthDifferenceLaw {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    charFun (normalizedDistinctDepthDifferenceLaw n) t =
      (distinctDepthDifferenceCosine n (depthDifferenceFrequency t n) : ℂ) := by
  rw [charFun_apply_real]
  change (∫ y : ℝ, Complex.exp ((t : ℂ) * y * Complex.I)
    ∂(distinctDepthDifferenceLaw n).map
      (fun z : ℤ => (z : ℝ) / Real.sqrt (Real.log n))) = _
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ z : ℤ,
    Complex.exp ((t : ℂ) * (((z : ℝ) / Real.sqrt (Real.log n) : ℝ) : ℂ) * Complex.I)
      ∂distinctDepthDifferenceLaw n) = _
  have he (z : ℤ) :
      Complex.exp ((t : ℂ) * (((z : ℝ) / Real.sqrt (Real.log n) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((depthDifferenceFrequency t n * z : ℝ) : ℂ) * Complex.I) := by
    congr 1
    unfold depthDifferenceFrequency
    push_cast
    ring
  simp_rw [he]
  have hi : Integrable (fun z : ℤ =>
      Complex.exp (((depthDifferenceFrequency t n * z : ℝ) : ℂ) * Complex.I))
        (distinctDepthDifferenceLaw n) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun z => by
      rw [Complex.norm_exp_ofReal_mul_I]
  rw [← integral_re_add_im hi]
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    distinctDepthDifferenceLaw_integral_sin hn]
  simp [distinctDepthDifferenceCosine]

theorem charFun_gaussian_variance_two (t : ℝ) :
    charFun (gaussianReal 0 (2 : ℝ≥0)) t = (Real.exp (-(t ^ 2)) : ℂ) := by
  rw [charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem tendsto_charFun_normalizedDistinctDepthDifferenceLaw (t : ℝ) :
    Tendsto (fun n => charFun (normalizedDistinctDepthDifferenceLaw n) t) atTop
      (𝓝 (charFun (gaussianReal 0 (2 : ℝ≥0)) t)) := by
  rw [charFun_gaussian_variance_two]
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_distinctDepthDifferenceCosine_normalized t)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (charFun_normalizedDistinctDepthDifferenceLaw hn t).symm

/-- E4: the actual distinct-vertex depth difference has the claimed Gaussian limit. -/
theorem depthDifference_central_limit :
    Tendsto normalizedDistinctDepthDifferenceLaw atTop
      (𝓝 (⟨gaussianReal 0 (2 : ℝ≥0), inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  exact tendsto_charFun_normalizedDistinctDepthDifferenceLaw

/-- The equivalent random-variable formulation, with the actual sampled laws. -/
theorem depthDifference_tendstoInDistribution :
    TendstoInDistribution
      (fun (n : ℕ) (z : ℤ) => (z : ℝ) / Real.sqrt (Real.log n)) atTop
      (fun y : ℝ => y) (fun n => distinctDepthDifferenceLaw n) (gaussianReal 0 (2 : ℝ≥0)) := by
  apply TendstoInDistribution.of_tendsto_charFun (fun _ => by fun_prop) (by fun_prop)
  intro t
  rw [show (fun y : ℝ => y) = id from rfl, Measure.map_id]
  simpa only [normalizedDistinctDepthDifferenceLaw,
    ProbabilityMeasure.coe_mk] using tendsto_charFun_normalizedDistinctDepthDifferenceLaw t

end FreezingGrowth.RRT
