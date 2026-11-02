module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniqueness for the bounded scalar first-birth equation

The proof iterates the Volterra inequality to obtain a factorial bound.
Continuity of the initially measurable solutions is not an assumption.
-/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory Filter Set
open scoped Topology

/-- Bounded measurable functions on the positive half-line are integrable on
each compact interval starting at zero. -/
theorem intervalIntegrable_of_nonnegative_bounded {f : ℝ → ℝ} {t C : ℝ}
    (ht : 0 ≤ t) (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hb : ∀ u ∈ Icc 0 t, ‖f u‖ ≤ C) : IntervalIntegrable f volume 0 t := by
  have hm : AEStronglyMeasurable f (volume.restrict (Icc 0 t)) :=
    hf.mono_measure (Measure.restrict_mono_set volume (fun _ hu => hu.1))
  have hi : IntegrableOn f (Icc 0 t) := by
    apply Integrable.mono' (integrable_const C) hm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hb u hu
  exact (show IntegrableOn f (uIcc 0 t) from by
    simpa only [uIcc_of_le ht] using hi).intervalIntegrable

/-- The homogeneous Volterra inequality has no nonzero bounded solution. -/
theorem eq_zero_of_volterra_le {f : ℝ → ℝ}
    (hnon : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hbound : ∀ t, 0 ≤ t → f t ≤ 1)
    (hint : ∀ t, 0 ≤ t → IntervalIntegrable f volume 0 t)
    (hvol : ∀ t, 0 ≤ t → f t ≤ ∫ u in (0 : ℝ)..t, f u) :
    ∀ t, 0 ≤ t → f t = 0 := by
  have hfact : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → f t ≤ t ^ k / (k.factorial : ℝ) := by
    intro k
    induction k with
    | zero => intro t ht; simpa using hbound t ht
    | succ k ih =>
      intro t ht
      calc
        f t ≤ ∫ u in (0 : ℝ)..t, f u := hvol t ht
        _ ≤ ∫ u in (0 : ℝ)..t, u ^ k / (k.factorial : ℝ) := by
          apply intervalIntegral.integral_mono_on ht (hint t ht)
            ((by fun_prop : Continuous (fun u : ℝ => u ^ k / (k.factorial : ℝ))).intervalIntegrable _ _)
          intro u hu
          exact ih u hu.1
        _ = t ^ (k + 1) / ((k + 1).factorial : ℝ) := by
          rw [intervalIntegral.integral_div, integral_pow]
          simp only [zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.factorial_succ,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp
  intro t ht
  apply le_antisymm _ (hnon t ht)
  exact ge_of_tendsto (Real.summable_pow_div_factorial t).tendsto_atTop_zero
    (Filter.Eventually.of_forall (fun k => hfact k t ht))

private theorem abs_sub_le_one {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    |a - b| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

private theorem weighted_renewal_integrable {f r : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hr : AEStronglyMeasurable r (volume.restrict (Ici 0)))
    (hfb : ∀ u, 0 ≤ u → f u ∈ Icc 0 1)
    (hrb : ∀ u, 0 ≤ u → r u ∈ Icc 0 1) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => Real.exp u * f u * r u) volume 0 t := by
  apply intervalIntegrable_of_nonnegative_bounded ht
    ((Real.continuous_exp.aestronglyMeasurable.mul hf).mul hr)
    (C := Real.exp t)
  intro u hu
  obtain ⟨hf0, hf1⟩ := hfb u hu.1
  obtain ⟨hr0, hr1⟩ := hrb u hu.1
  change ‖Real.exp u * f u * r u‖ ≤ Real.exp t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (Real.exp_pos u).le hf0) hr0)]
  calc
    _ ≤ Real.exp u * 1 * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hf1 (Real.exp_pos u).le
      · exact hr1
      · exact hr0
      · positivity
    _ ≤ Real.exp t := by simpa using Real.exp_le_exp.mpr hu.2

/-- Uniqueness of bounded measurable probability-valued solutions of the
first-birth integral equation on nonnegative times. -/
theorem scalar_renewal_unique {f g r : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hg : AEStronglyMeasurable g (volume.restrict (Ici 0)))
    (hr : AEStronglyMeasurable r (volume.restrict (Ici 0)))
    (hfb : ∀ t, 0 ≤ t → f t ∈ Icc 0 1)
    (hgb : ∀ t, 0 ≤ t → g t ∈ Icc 0 1)
    (hrb : ∀ t, 0 ≤ t → r t ∈ Icc 0 1)
    (hfeq : ∀ t, 0 ≤ t → f t = Real.exp (-t) *
      (1 + ∫ u in (0 : ℝ)..t, Real.exp u * f u * r u))
    (hgeq : ∀ t, 0 ≤ t → g t = Real.exp (-t) *
      (1 + ∫ u in (0 : ℝ)..t, Real.exp u * g u * r u)) :
    EqOn f g (Ici 0) := by
  have hdiff_int (t : ℝ) (ht : 0 ≤ t) :
      IntervalIntegrable (fun u => |f u - g u|) volume 0 t := by
    apply intervalIntegrable_of_nonnegative_bounded ht
      (continuous_abs.comp_aestronglyMeasurable (hf.sub hg)) (C := 1)
    intro u hu
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_sub_le_one (hfb u hu.1) (hgb u hu.1)
  have hvol (t : ℝ) (ht : 0 ≤ t) :
      |f t - g t| ≤ ∫ u in (0 : ℝ)..t, |f u - g u| := by
    let w : ℝ → ℝ := fun u => Real.exp (u - t) * (f u - g u) * r u
    have hwbound (u : ℝ) (hu : u ∈ Icc 0 t) : ‖w u‖ ≤ |f u - g u| := by
      have hr0 := (hrb u hu.1).1
      have hr1 := (hrb u hu.1).2
      have he0 := (Real.exp_pos (u - t)).le
      have he1 : Real.exp (u - t) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr hu.2)
      change |Real.exp (u - t) * (f u - g u) * r u| ≤ |f u - g u|
      rw [abs_mul, abs_mul, abs_of_nonneg he0, abs_of_nonneg hr0]
      calc
        _ ≤ 1 * |f u - g u| * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right he1 (abs_nonneg _)) hr1 hr0 (by positivity)
        _ = _ := by ring
    have hw : IntervalIntegrable w volume 0 t := by
      apply intervalIntegrable_of_nonnegative_bounded ht
        (((by fun_prop : Continuous (fun u : ℝ => Real.exp (u - t))).aestronglyMeasurable.mul
          (hf.sub hg)).mul hr) (C := 1)
      intro u hu
      exact (hwbound u hu).trans (abs_sub_le_one (hfb u hu.1) (hgb u hu.1))
    have he : f t - g t = ∫ u in (0 : ℝ)..t, w u := by
      rw [hfeq t ht, hgeq t ht, ← mul_sub, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub
          (weighted_renewal_integrable hf hr hfb hrb ht)
          (weighted_renewal_integrable hg hr hgb hrb ht),
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp [w]
      rw [Real.exp_sub, Real.exp_neg]
      ring
    rw [he, ← Real.norm_eq_abs]
    exact (intervalIntegral.norm_integral_le_integral_norm ht).trans
      (intervalIntegral.integral_mono_on ht hw.norm (hdiff_int t ht) hwbound)
  have hz := eq_zero_of_volterra_le (fun _ _ => abs_nonneg _)
    (fun t ht => abs_sub_le_one (hfb t ht) (hgb t ht)) hdiff_int hvol
  intro t ht
  exact sub_eq_zero.mp (abs_eq_zero.mp (hz t ht))

end FreezingGrowth
