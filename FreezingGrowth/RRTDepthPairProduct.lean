module

public import FreezingGrowth.RRTDepthPairCosine
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The Gaussian limit of the scalar Bernoulli-difference product. Real
logarithm inequalities suffice; no complex logarithm or array CLT is assumed. -/

@[expose] public section
namespace FreezingGrowth.RRT

open Filter
open scoped Topology

noncomputable def depthDifferenceVarianceSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, depthBernoulliParameter k * (1 - depthBernoulliParameter k)

theorem depthDifferenceVarianceSum_eq (n : ℕ) :
    depthDifferenceVarianceSum n = depthMean n -
      ∑ k ∈ Finset.range n, depthBernoulliParameter k ^ 2 := by
  induction n with
  | zero => simp [depthDifferenceVarianceSum]
  | succ n ih =>
    rw [depthDifferenceVarianceSum, Finset.sum_range_succ]
    change depthDifferenceVarianceSum n + _ = _
    rw [ih, depthMean_succ, Finset.sum_range_succ]
    ring

theorem tendsto_depthDifferenceVarianceSum_div_log :
    Tendsto (fun n : ℕ => depthDifferenceVarianceSum n / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := summable_depthBernoulliParameter_sq.hasSum.tendsto_sum_nat.div_atTop hlog
  have h := depthMean_div_log_tendsto_one.sub hs
  simpa only [sub_zero, depthDifferenceVarianceSum_eq, sub_div] using h

noncomputable def depthDifferenceCosineLoss (t : ℝ) : ℝ := 2 * (1 - Real.cos t)

theorem depthDifferenceCosineLoss_nonneg (t : ℝ) : 0 ≤ depthDifferenceCosineLoss t := by
  unfold depthDifferenceCosineLoss
  have := Real.cos_le_one t
  linarith

theorem depthDifferenceCosineLoss_eq_sinc (t : ℝ) :
    depthDifferenceCosineLoss t = t ^ 2 * Real.sinc (t / 2) ^ 2 := by
  by_cases ht : t = 0
  · simp [ht, depthDifferenceCosineLoss]
  · rw [Real.sinc_of_ne_zero (div_ne_zero ht (by norm_num))]
    have hc : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      simpa only [show 2 * (t / 2) = t by ring] using
        (Real.cos_two_mul_eq_one_sub (x := t / 2))
    rw [depthDifferenceCosineLoss, hc]
    field_simp
    ring

theorem depthDifferenceIdealFactor_eq_loss (k : ℕ) (t : ℝ) :
    depthDifferenceIdealFactor k t = 1 - depthDifferenceCosineLoss t *
      (depthBernoulliParameter k * (1 - depthBernoulliParameter k)) := by
  unfold depthDifferenceIdealFactor depthDifferenceCosineLoss
  ring

private theorem variance_parameter_bounds (k : ℕ) :
    0 ≤ depthBernoulliParameter k * (1 - depthBernoulliParameter k) ∧
      depthBernoulliParameter k * (1 - depthBernoulliParameter k) ≤ 1 / 4 := by
  have hp := (depthBernoulliParameter_pos k).le
  have hp' := depthBernoulliParameter_le_half k
  constructor
  · exact mul_nonneg hp (by linarith)
  · nlinarith [sq_nonneg (depthBernoulliParameter k - 1 / 2)]

theorem depthDifferenceIdealFactor_pos_of_loss_le_one {t : ℝ}
    (ht : depthDifferenceCosineLoss t ≤ 1) (k : ℕ) :
    0 < depthDifferenceIdealFactor k t := by
  rw [depthDifferenceIdealFactor_eq_loss]
  have hb := variance_parameter_bounds k
  have ha := depthDifferenceCosineLoss_nonneg t
  have hh := mul_le_mul ht hb.2 hb.1 (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

theorem depthDifferenceIdealProduct_pos_of_loss_le_one {t : ℝ}
    (ht : depthDifferenceCosineLoss t ≤ 1) (n : ℕ) :
    0 < depthDifferenceIdealProduct n t :=
  Finset.prod_pos fun k _ => depthDifferenceIdealFactor_pos_of_loss_le_one ht k

private theorem log_one_sub_product_bounds {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1 / 4) :
    -(a * b) / (1 - a / 4) ≤ Real.log (1 - a * b) ∧
      Real.log (1 - a * b) ≤ -(a * b) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hab1 : a * b ≤ 1 / 4 := by
    calc a * b ≤ 1 * (1 / 4) := mul_le_mul ha1 hb1 hb (by norm_num)
         _ = _ := by ring
  have hden : 0 < 1 - a * b := by linarith
  have hden' : 0 < 1 - a / 4 := by linarith
  have hmono : 1 - a / 4 ≤ 1 - a * b := by nlinarith
  constructor
  · have hlog := Real.one_sub_inv_le_log_of_pos hden
    have hid : 1 - (1 - a * b)⁻¹ = -(a * b) / (1 - a * b) := by
      field_simp
      ring
    rw [hid] at hlog
    simpa only [neg_div] using
      (neg_le_neg (div_le_div_of_nonneg_left hab hden' hmono)).trans
        (by simpa only [neg_div] using hlog)
  · have h := Real.log_le_sub_one_of_pos hden
    linarith

theorem depthDifferenceIdealProduct_log_bounds (n : ℕ) {t : ℝ}
    (ht : depthDifferenceCosineLoss t ≤ 1) :
    -(depthDifferenceCosineLoss t * depthDifferenceVarianceSum n) /
        (1 - depthDifferenceCosineLoss t / 4) ≤ Real.log (depthDifferenceIdealProduct n t) ∧
      Real.log (depthDifferenceIdealProduct n t) ≤
        -(depthDifferenceCosineLoss t * depthDifferenceVarianceSum n) := by
  have he : Real.log (depthDifferenceIdealProduct n t) =
      ∑ k ∈ Finset.range n, Real.log (1 - depthDifferenceCosineLoss t *
        (depthBernoulliParameter k * (1 - depthBernoulliParameter k))) := by
    unfold depthDifferenceIdealProduct
    rw [Real.log_prod (fun k _ => (depthDifferenceIdealFactor_pos_of_loss_le_one ht k).ne')]
    simp_rw [depthDifferenceIdealFactor_eq_loss]
  rw [he]
  have hl := Finset.sum_le_sum (s := Finset.range n) (fun k _ =>
    (log_one_sub_product_bounds (depthDifferenceCosineLoss_nonneg t) ht
      (variance_parameter_bounds k).1 (variance_parameter_bounds k).2).1)
  have hu := Finset.sum_le_sum (s := Finset.range n) (fun k _ =>
    (log_one_sub_product_bounds (depthDifferenceCosineLoss_nonneg t) ht
      (variance_parameter_bounds k).1 (variance_parameter_bounds k).2).2)
  simp only [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.mul_sum] at hl hu
  simpa only [depthDifferenceVarianceSum] using And.intro hl hu

noncomputable def depthDifferenceFrequency (t : ℝ) (n : ℕ) : ℝ :=
  t / Real.sqrt (Real.log (n : ℝ))

theorem tendsto_depthDifferenceFrequency (t : ℝ) :
    Tendsto (depthDifferenceFrequency t) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem depthDifferenceCosineLoss_mul_log {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    depthDifferenceCosineLoss (depthDifferenceFrequency t n) * Real.log (n : ℝ) =
      t ^ 2 * Real.sinc (depthDifferenceFrequency t n / 2) ^ 2 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hs : Real.sqrt (Real.log (n : ℝ)) ^ 2 = Real.log (n : ℝ) := Real.sq_sqrt hl.le
  rw [depthDifferenceCosineLoss_eq_sinc]
  unfold depthDifferenceFrequency
  rw [div_pow, hs]
  field_simp

theorem tendsto_depthDifferenceCosineLoss_mul_log (t : ℝ) :
    Tendsto (fun n : ℕ => depthDifferenceCosineLoss (depthDifferenceFrequency t n) * Real.log n)
      atTop (𝓝 (t ^ 2)) := by
  have ht : Tendsto (fun n => depthDifferenceFrequency t n / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_depthDifferenceFrequency t).div_const 2
  have hs := ((Real.continuous_sinc.tendsto 0).comp ht).pow 2
  have h := hs.const_mul (t ^ 2)
  simp only [Real.sinc_zero, one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (depthDifferenceCosineLoss_mul_log hn t).symm

theorem tendsto_depthDifferenceCosineLoss (t : ℝ) :
    Tendsto (fun n => depthDifferenceCosineLoss (depthDifferenceFrequency t n))
      atTop (𝓝 0) := by
  have hcos := (Real.continuous_cos.tendsto 0).comp (tendsto_depthDifferenceFrequency t)
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hcos).const_mul 2
  simpa only [Function.comp_def, Real.cos_zero, sub_self, mul_zero, depthDifferenceCosineLoss] using h

/-- The comparator has limiting variance two on the paper's `sqrt(log n)` scale. -/
theorem tendsto_depthDifferenceIdealProduct (t : ℝ) :
    Tendsto (fun n => depthDifferenceIdealProduct n (depthDifferenceFrequency t n))
      atTop (𝓝 (Real.exp (-(t ^ 2)))) := by
  have ha := tendsto_depthDifferenceCosineLoss t
  have hEV : Tendsto (fun n => depthDifferenceCosineLoss (depthDifferenceFrequency t n) *
      depthDifferenceVarianceSum n) atTop (𝓝 (t ^ 2)) := by
    have h := (tendsto_depthDifferenceCosineLoss_mul_log t).mul
      tendsto_depthDifferenceVarianceSum_div_log
    simp only [mul_one] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by
      exact_mod_cast (show 1 < n by omega))).ne'
    field_simp
  have hden : Tendsto (fun n => 1 - depthDifferenceCosineLoss (depthDifferenceFrequency t n) / 4)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub (ha.div_const 4)
  have hlow := hEV.neg.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hlow
  have hsmall : ∀ᶠ n in atTop, depthDifferenceCosineLoss (depthDifferenceFrequency t n) ≤ 1 :=
    ha.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlog : Tendsto (fun n => Real.log (depthDifferenceIdealProduct n (depthDifferenceFrequency t n)))
      atTop (𝓝 (-(t ^ 2))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hEV.neg
    · exact hsmall.mono fun n hn => (depthDifferenceIdealProduct_log_bounds n hn).1
    · exact hsmall.mono fun n hn => (depthDifferenceIdealProduct_log_bounds n hn).2
  have hexp : Tendsto
      (fun n => Real.exp (Real.log (depthDifferenceIdealProduct n (depthDifferenceFrequency t n))))
      atTop (𝓝 (Real.exp (-(t ^ 2)))) := by
    simpa only [Function.comp_def] using (Real.continuous_exp.tendsto (-(t ^ 2))).comp hlog
  apply hexp.congr'
  filter_upwards [hsmall] with n hn
  exact Real.exp_log (depthDifferenceIdealProduct_pos_of_loss_le_one hn n)

theorem tendsto_depthDifferenceCosine_normalized (t : ℝ) :
    Tendsto (fun n => depthDifferenceCosine n (depthDifferenceFrequency t n))
      atTop (𝓝 (Real.exp (-(t ^ 2)))) := by
  have h := (tendsto_depthDifferenceCosine_sub_product (tendsto_depthDifferenceFrequency t)).add
    (tendsto_depthDifferenceIdealProduct t)
  simpa only [sub_add_cancel, zero_add] using h

end FreezingGrowth.RRT
