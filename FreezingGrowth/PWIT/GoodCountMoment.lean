module

public import FreezingGrowth.PWIT.GoodPaths

/-!
# Conditional second-moment assembly for the actual finite good count

This module proves the algebraic and event implications of the two moment
estimates. The first-moment lower bound and the per-path overlap bound remain
explicit hypotheses; neither barrier estimates nor overlap estimates are
asserted here.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

theorem integral_goodCount_eq_sum (d : ℕ) (a : ℝ) :
    (∫ ω, goodCount d a ω ∂law) =
      ∑ v ∈ rankWindow d, law.real (goodEvent d a v) := by
  unfold goodCount
  rw [integral_finsetSum _ fun v _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_goodEvent d a v)]
  apply Finset.sum_congr rfl
  intro v _
  rw [integral_indicator_const (μ := law) (1 : ℝ) (measurableSet_goodEvent d a v)]
  simp

theorem goodCount_sq_eq_sum (d : ℕ) (a : ℝ) (ω : Sample) :
    goodCount d a ω ^ 2 =
      ∑ v ∈ rankWindow d, (goodEvent d a v).indicator (goodCount d a) ω := by
  calc
    _ = goodCount d a ω *
        ∑ v ∈ rankWindow d, (goodEvent d a v).indicator (fun _ => (1 : ℝ)) ω := by
      rw [← goodCount, pow_two]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : ω ∈ goodEvent d a v <;> simp [hv]

theorem integral_goodCount_sq_le_of_pair_bound (d : ℕ) (a C : ℝ)
    (hpair : ∀ v ∈ rankWindow d,
      (∫ ω, (goodEvent d a v).indicator (goodCount d a) ω ∂law) ≤
        C * law.real (goodEvent d a v)) :
    (∫ ω, goodCount d a ω ^ 2 ∂law) ≤ C * ∫ ω, goodCount d a ω ∂law := by
  simp_rw [goodCount_sq_eq_sum]
  rw [integral_finsetSum _ fun v _ =>
    (integrable_goodCount d a).indicator (measurableSet_goodEvent d a v)]
  calc
    _ ≤ ∑ v ∈ rankWindow d, C * law.real (goodEvent d a v) := Finset.sum_le_sum hpair
    _ = _ := by rw [← Finset.mul_sum, integral_goodCount_eq_sum]

theorem goodCount_pos_subset_reaches (d : ℕ) (a : ℝ) :
    {ω | 0 < goodCount d a ω} ⊆ reaches d (timeCenter d) := by
  intro ω hω
  change 0 < ∑ v ∈ rankWindow d,
    (goodEvent d a v).indicator (fun _ => (1 : ℝ)) ω at hω
  obtain ⟨v, hv, hpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun v (_ : v ∈ rankWindow d) =>
      Set.indicator_nonneg (fun (_ : Sample) _ => (by norm_num : (0 : ℝ) ≤ 1)) ω)).mp hω
  have hg : ω ∈ goodEvent d a v := by
    by_contra hnot
    simp [hnot] at hpos
  exact ⟨v, (mem_rankWindow.mp hv).1, hg.2.1⟩

/-- A polynomial form of the second-moment argument. It never divides by a
possibly zero success probability. -/
theorem goodCount_probability_lower_of_moments (d : ℕ) (a C c : ℝ)
    (hC : 0 < C) (hfirst : c ≤ ∫ ω, goodCount d a ω ∂law)
    (hsecond : (∫ ω, goodCount d a ω ^ 2 ∂law) ≤
      C * ∫ ω, goodCount d a ω ∂law) :
    c / C ≤ law.real {ω | 0 < goodCount d a ω} := by
  let E : Set Sample := {ω | 0 < goodCount d a ω}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (measurable_goodCount d a)
  have hI : Integrable (E.indicator (fun _ => (1 : ℝ))) law :=
    (integrable_const (1 : ℝ)).indicator hE
  have hQ : 0 ≤ ∫ ω, goodCount d a ω ^ 2 - 2 * C * goodCount d a ω +
      C ^ 2 * E.indicator (fun _ => (1 : ℝ)) ω ∂law := by
    apply integral_nonneg
    intro ω
    change (0 : ℝ) ≤ goodCount d a ω ^ 2 - 2 * C * goodCount d a ω +
      C ^ 2 * E.indicator (fun _ => (1 : ℝ)) ω
    by_cases hω : ω ∈ E
    · simp only [Set.indicator_of_mem hω, mul_one]
      nlinarith [sq_nonneg (goodCount d a ω - C)]
    · have hz : goodCount d a ω = 0 := by
        exact le_antisymm (le_of_not_gt hω) (goodCount_nonneg d a ω)
      simp [Set.indicator_of_notMem hω, hz]
  have hsub : Integrable (fun ω => goodCount d a ω ^ 2 - 2 * C * goodCount d a ω) law :=
    (integrable_goodCount_sq d a).sub ((integrable_goodCount d a).const_mul (2 * C))
  rw [integral_add hsub (hI.const_mul (C ^ 2)),
    integral_sub (integrable_goodCount_sq d a)
      ((integrable_goodCount d a).const_mul (2 * C)),
    integral_const_mul, integral_const_mul,
    integral_indicator_const (μ := law) (1 : ℝ) hE] at hQ
  simp only [smul_eq_mul, mul_one] at hQ
  rw [div_le_iff₀ hC]
  have hmain : C * (∫ ω, goodCount d a ω ∂law) ≤ C ^ 2 * law.real E := by
    linarith
  have hmean : (∫ ω, goodCount d a ω ∂law) ≤ C * law.real E := by
    apply (mul_le_mul_iff_left₀ hC).mp
    nlinarith [hmain]
  simpa only [E, mul_comm] using hfirst.trans hmean

theorem reaches_probability_lower_of_goodCount_bounds (d : ℕ) (a C c : ℝ)
    (hC : 0 < C) (hfirst : c ≤ ∫ ω, goodCount d a ω ∂law)
    (hpair : ∀ v ∈ rankWindow d,
      (∫ ω, (goodEvent d a v).indicator (goodCount d a) ω ∂law) ≤
        C * law.real (goodEvent d a v)) :
    c / C ≤ law.real (reaches d (timeCenter d)) :=
  (goodCount_probability_lower_of_moments d a C c hC hfirst
    (integral_goodCount_sq_le_of_pair_bound d a C hpair)).trans
      (measureReal_mono (goodCount_pos_subset_reaches d a))

end FreezingGrowth.PWIT
