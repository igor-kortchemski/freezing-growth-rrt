module

public import FreezingGrowth.RRTGeometricMixture
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Analytic generating functions for the geometric recursive-tree mixture. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable def heightCdfCoefficient (h n : ℕ) : ℝ :=
  (Forward.heightLaw allAttach n).real {a | a ≤ h}

theorem heightCdfCoefficient_nonneg (h n : ℕ) : 0 ≤ heightCdfCoefficient h n :=
  measureReal_nonneg

theorem heightCdfCoefficient_le_one (h n : ℕ) : heightCdfCoefficient h n ≤ 1 :=
  measureReal_le_one

@[simp] theorem heightCdfCoefficient_initial (h : ℕ) : heightCdfCoefficient h 0 = 1 :=
  RRTSplit.heightLaw_cdf_initial h

@[simp] theorem heightCdfCoefficient_zero_succ (n : ℕ) :
    heightCdfCoefficient 0 (n + 1) = 0 := RRTSplit.heightLaw_cdf_zero n

noncomputable def heightCdfGenerating (h : ℕ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, heightCdfCoefficient h n * z ^ n

private theorem bounded_powerSeries_summable (a : ℕ → ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1) {z : ℝ} (hz : ‖z‖ < 1) :
    Summable (fun n => a n * z ^ n) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz)
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n) (ha n)

private theorem summable_succ_mul_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
  have hq : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  simpa only [add_mul, one_mul] using
    (hasSum_coe_mul_geometric_of_norm_lt_one hq).summable.add
      (summable_geometric_of_lt_one hq0 hq1)

private theorem hasDerivAt_bounded_powerSeries (a : ℕ → ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1) {z : ℝ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun x => ∑' n : ℕ, a n * x ^ n)
      (∑' n : ℕ, a (n + 1) * (((n : ℝ) + 1) * z ^ n)) z := by
  simp only [Real.norm_eq_abs] at hz
  let q : ℝ := (‖z‖ + 1) / 2
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hzq : ‖z‖ < q := by dsimp [q]; linarith
  have hbound : ∀ n (x : ℝ), x ∈ Ioo (-q) q →
      ‖a (n + 1) * (((n : ℝ) + 1) * x ^ n)‖ ≤ ((n : ℝ) + 1) * q ^ n := by
    intro n x hx
    have hxq : ‖x‖ ≤ q := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hx.1.le, hx.2.le⟩
    rw [norm_mul, norm_mul, norm_pow,
      Real.norm_eq_abs ((n : ℝ) + 1), abs_of_nonneg (by positivity)]
    calc
      _ ≤ 1 * (((n : ℝ) + 1) * ‖x‖ ^ n) :=
        mul_le_mul_of_nonneg_right (ha _) (by positivity)
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg x) hxq n) (by positivity : 0 ≤ (n : ℝ) + 1)
  have hzmem : z ∈ Ioo (-q) q := by
    rw [Real.norm_eq_abs, abs_lt] at hzq
    exact hzq
  have hder := hasDerivAt_tsum_of_isPreconnected
    (g := fun n x => a (n + 1) * x ^ (n + 1))
    (g' := fun n x => a (n + 1) * (((n : ℝ) + 1) * x ^ n))
    (summable_succ_mul_pow hq0.le hq1) isOpen_Ioo (convex_Ioo (-q) q).isPreconnected
    (fun n x _ => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply, id_eq, mul_one] using
        ((hasDerivAt_id x).pow (n + 1)).const_mul (a (n + 1)))
    hbound (show (0 : ℝ) ∈ Ioo (-q) q by constructor <;> linarith)
    (by simp : Summable (fun n : ℕ => a (n + 1) * (0 : ℝ) ^ (n + 1))) hzmem
  apply (hder.const_add (a 0)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hzmem.1 hzmem.2] with x hx
  have hxn : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact (abs_lt.mpr hx).trans hq1
  simpa only [pow_zero, mul_one] using
    (bounded_powerSeries_summable a ha hxn).tsum_eq_zero_add

theorem heightCdfGenerating_summable (h : ℕ) {z : ℝ} (hz : ‖z‖ < 1) :
    Summable (fun n => heightCdfCoefficient h n * z ^ n) :=
  bounded_powerSeries_summable _ (fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (heightCdfCoefficient_nonneg h n)]
    exact heightCdfCoefficient_le_one h n) hz

theorem heightCdfGenerating_hasDerivAt (h : ℕ) {z : ℝ} (hz : ‖z‖ < 1) :
    HasDerivAt (heightCdfGenerating h)
      (∑' n : ℕ, heightCdfCoefficient h (n + 1) * (((n : ℝ) + 1) * z ^ n)) z :=
  hasDerivAt_bounded_powerSeries _ (fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (heightCdfCoefficient_nonneg h n)]
    exact heightCdfCoefficient_le_one h n) hz

private theorem heightCdfGenerating_summable_norm (h : ℕ) {z : ℝ} (hz : ‖z‖ < 1) :
    Summable (fun n => ‖heightCdfCoefficient h n * z ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) (summable_geometric_of_lt_one (norm_nonneg z) hz)
  rw [norm_mul, norm_pow, Real.norm_eq_abs (heightCdfCoefficient h n),
    abs_of_nonneg (heightCdfCoefficient_nonneg h n)]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n)
    (heightCdfCoefficient_le_one h n)

/-- The exact CDF recurrence becomes an ordinary differential equation. -/
theorem heightCdfGenerating_succ_hasDerivAt (h : ℕ) {z : ℝ} (hz : ‖z‖ < 1) :
    HasDerivAt (heightCdfGenerating (h + 1))
      (heightCdfGenerating (h + 1) z * heightCdfGenerating h z) z := by
  apply (heightCdfGenerating_hasDerivAt (h + 1) hz).congr_deriv
  unfold heightCdfGenerating
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (heightCdfGenerating_summable_norm (h + 1) hz)
    (heightCdfGenerating_summable_norm h hz)]
  apply tsum_congr
  intro n
  have hr := RRTSplit.heightLaw_cdf_succ n h
  change heightCdfCoefficient (h + 1) (n + 1) =
    (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1),
      heightCdfCoefficient (h + 1) k * heightCdfCoefficient h (n - k) at hr
  rw [hr]
  have hcancel (S : ℝ) : (1 / ((n : ℝ) + 1) * S) * (((n : ℝ) + 1) * z ^ n) =
      S * z ^ n := by
    field_simp
  rw [hcancel]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : z ^ k * z ^ (n - k) = z ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  calc
    _ = (heightCdfCoefficient (h + 1) k * heightCdfCoefficient h (n - k)) *
        (z ^ k * z ^ (n - k)) := by rw [hp]
    _ = _ := by ring

@[simp] theorem heightCdfGenerating_at_zero (h : ℕ) : heightCdfGenerating h 0 = 1 := by
  unfold heightCdfGenerating
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- The series represents the actual geometric mixture, not a new height law. -/
theorem geometricHeightLaw_cdf_eq_generating (t : ℝ≥0) (h : ℕ) :
    (geometricHeightLaw t).real {a | a ≤ h} =
      Real.exp (-(t : ℝ)) * heightCdfGenerating h (1 - Real.exp (-(t : ℝ))) := by
  rw [geometricHeightLaw_real_series, heightCdfGenerating, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold heightCdfCoefficient
  ring

/-- A real-time extension of the CDF expression. Probability interpretation is
asserted only for nonnegative times. -/
noncomputable def geometricCdf (h : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t) * heightCdfGenerating h (1 - Real.exp (-t))

theorem geometricCdf_eq_heightLaw (t : ℝ≥0) (h : ℕ) :
    geometricCdf h (t : ℝ) = (geometricHeightLaw t).real {a | a ≤ h} :=
  (geometricHeightLaw_cdf_eq_generating t h).symm

theorem geometricCdf_nonneg (h : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ geometricCdf h t := by
  have he := geometricCdf_eq_heightLaw (⟨t, ht⟩ : ℝ≥0) h
  change geometricCdf h t = _ at he
  rw [he]
  exact measureReal_nonneg

theorem geometricCdf_le_one (h : ℕ) {t : ℝ} (ht : 0 ≤ t) : geometricCdf h t ≤ 1 := by
  let := geometricHeightLaw_isProbabilityMeasure (⟨t, ht⟩ : ℝ≥0)
  have he := geometricCdf_eq_heightLaw (⟨t, ht⟩ : ℝ≥0) h
  change geometricCdf h t = _ at he
  rw [he]
  exact measureReal_le_one

theorem geometricHeightLaw_tail_eq_one_sub_cdf (t : ℝ≥0) (h : ℕ) :
    (geometricHeightLaw t).real {a | h + 1 ≤ a} = 1 - geometricCdf h (t : ℝ) := by
  have he : {a : ℕ | h + 1 ≤ a} = {a : ℕ | a ≤ h}ᶜ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    omega
  rw [he, measureReal_compl (Set.to_countable _).measurableSet, probReal_univ,
    geometricCdf_eq_heightLaw]

@[simp] theorem geometricCdf_initial (h : ℕ) : geometricCdf h 0 = 1 := by
  simp [geometricCdf]

@[simp] theorem heightCdfGenerating_zero (z : ℝ) : heightCdfGenerating 0 z = 1 := by
  unfold heightCdfGenerating
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp

@[simp] theorem geometricCdf_zero (t : ℝ) : geometricCdf 0 t = Real.exp (-t) := by
  simp [geometricCdf]

theorem geometricCdf_succ_hasDerivAt (h : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (geometricCdf (h + 1))
      (-geometricCdf (h + 1) t + geometricCdf (h + 1) t * geometricCdf h t) t := by
  have hz : ‖1 - Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)))]
    linarith [Real.exp_pos (-t)]
  have hd := (heightCdfGenerating_succ_hasDerivAt h hz).comp t
    (((hasDerivAt_id t).neg.exp).const_sub 1)
  have hm := ((hasDerivAt_id t).neg.exp).mul hd
  change HasDerivAt (geometricCdf (h + 1)) _ t at hm
  apply hm.congr_deriv
  dsimp [geometricCdf]
  ring

theorem geometricCdf_continuousOn (h : ℕ) : ContinuousOn (geometricCdf h) (Ici 0) := by
  cases h with
  | zero =>
    rw [show geometricCdf 0 = (fun t : ℝ => Real.exp (-t)) from funext geometricCdf_zero]
    fun_prop
  | succ h =>
    intro t ht
    exact (geometricCdf_succ_hasDerivAt h ht).continuousAt.continuousWithinAt

/-- Integrating-factor form of the scalar renewal equation. -/
theorem geometricCdf_renewal_integratingFactor (h : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    geometricCdf (h + 1) t = Real.exp (-t) + Real.exp (-t) *
      ∫ u in (0 : ℝ)..t, Real.exp u * geometricCdf (h + 1) u * geometricCdf h u := by
  have hd (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt (fun u => Real.exp u * geometricCdf (h + 1) u)
        (Real.exp u * geometricCdf (h + 1) u * geometricCdf h u) u := by
    convert (Real.hasDerivAt_exp u).mul (geometricCdf_succ_hasDerivAt h hu) using 1
    ring
  have hcont (j : ℕ) : ContinuousOn (geometricCdf j) (Icc 0 t) :=
    (geometricCdf_continuousOn j).mono (fun _ hx => hx.1)
  have hi : IntervalIntegrable (fun u =>
      Real.exp u * geometricCdf (h + 1) u * geometricCdf h u) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht
      ((Real.continuous_exp.continuousOn.mul (hcont (h + 1))).mul (hcont h))
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u ((show u ∈ Icc 0 t by simpa only [uIcc_of_le ht] using hu).1)) hi
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  simp only [Real.exp_zero, geometricCdf_initial, mul_one] at hf
  rw [hf, mul_sub, ← mul_assoc, he]
  ring

/-- First-birth renewal equation in the same form as the branching decomposition. -/
theorem geometricCdf_renewal (h : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    geometricCdf (h + 1) t = Real.exp (-t) +
      ∫ s in (0 : ℝ)..t, Real.exp (-s) *
        geometricCdf (h + 1) (t - s) * geometricCdf h (t - s) := by
  rw [geometricCdf_renewal_integratingFactor h ht, ← intervalIntegral.integral_const_mul]
  congr 1
  have hc := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => Real.exp (-t) * (Real.exp u *
      geometricCdf (h + 1) u * geometricCdf h u)) (a := (0 : ℝ)) (b := t) t
  simp only [sub_self, sub_zero] at hc
  rw [← hc]
  apply intervalIntegral.integral_congr
  intro s _
  have he : Real.exp (-t) * Real.exp (t - s) = Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-t) * Real.exp (t - s)) *
      geometricCdf (h + 1) (t - s) * geometricCdf h (t - s) := by ring
    _ = _ := by rw [he]

/-- The elementary integral underlying the geometric generating-function bridge. -/
theorem integral_geometric_kernel (r : ℕ) (t : ℝ) :
    (∫ u in (0 : ℝ)..t, Real.exp (-u) * (1 - Real.exp (-u)) ^ r) =
      (1 - Real.exp (-t)) ^ (r + 1) / ((r : ℝ) + 1) := by
  have hd (u : ℝ) :
      HasDerivAt (fun u : ℝ => (1 - Real.exp (-u)) ^ (r + 1) / ((r : ℝ) + 1))
        (Real.exp (-u) * (1 - Real.exp (-u)) ^ r) u := by
    have hd := (((((hasDerivAt_id u).neg).exp).const_sub 1).pow (r + 1)).div_const
      ((r : ℝ) + 1)
    change HasDerivAt (fun u : ℝ =>
      (1 - Real.exp (-u)) ^ (r + 1) / ((r : ℝ) + 1)) _ u at hd
    apply hd.congr_deriv
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.neg_apply, id_eq]
    field_simp
  have hi : IntervalIntegrable
      (fun u : ℝ => Real.exp (-u) * (1 - Real.exp (-u)) ^ r) volume 0 t :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-u) *
      (1 - Real.exp (-u)) ^ r)).intervalIntegrable _ _
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi

end FreezingGrowth.RRT
