module

public import FreezingGrowth.RRTBoundedHeight
public import FreezingGrowth.AlternatingStarProbability

/-! The threshold in Question 2 must diverge, if the proposed clipped
stochastic domination holds. This conditional necessity does not assert that
such a threshold exists. Thresholds and tail tests are genuinely real-valued. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory Filter
open scoped Topology

/-- The necessary threshold-divergence claim accompanying Question 2. The input
is the actual full real-tail comparison with every admissible word of size n. -/
def Question2ThresholdDivergenceClaim : Prop :=
  ∀ h : ℕ → ℝ,
    (∀ n : ℕ, 1 ≤ n → ∀ xs : Word, Word.InFamily n xs → ∀ r : ℝ,
      (Forward.heightLaw RRT.allAttach n).real {j | r ≤ (j : ℝ)} ≤
        xs.heightLaw.real {j | r ≤ max (h n) (j : ℝ)}) →
      Tendsto h atTop atTop

theorem alternating_star_real_mass_ge_half_pow {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ (alternatingWord n).heightLaw.real {1} := by
  rw [Alternating.height_one_real_mass hn]
  have hh : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ (n - 1) :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le n 1))
  simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow] using hh

/-- Fixed RRT heights are eventually less likely than the alternating star.
This uses actual laws and the exact alternating star probability. -/
theorem eventually_rrt_boundedHeight_lt_alternating_star (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (Forward.heightLaw RRT.allAttach n).real {j | j ≤ K} <
        (alternatingWord n).heightLaw.real {1} := by
  obtain ⟨D, _hD₀, hD⟩ := RRT.heightLaw_boundedHeight_le_geometric K (1 / 4) (by norm_num)
  have hp : Tendsto (fun n : ℕ => D * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul D
  have he : ∀ᶠ n : ℕ in atTop, D * (1 / 2 : ℝ) ^ n < 1 :=
    hp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn₁
  have hquarter : D * (1 / 4 : ℝ) ^ n < (1 / 2 : ℝ) ^ n := by
    have hh := mul_lt_mul_of_pos_right hn (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    have hpow : (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    rw [hpow]
    nlinarith
  exact (hD n).trans_lt (hquarter.trans_le (alternating_star_real_mass_ge_half_pow hn₁))

private theorem clipped_tail_comparison_forces_cdf {h : ℕ → ℝ} {n K : ℕ}
    (hK : 1 ≤ K) (hcut : h n ≤ (K : ℝ))
    (hdom : ∀ xs : Word, Word.InFamily n xs → ∀ r : ℝ,
      (Forward.heightLaw RRT.allAttach n).real {j | r ≤ (j : ℝ)} ≤
        xs.heightLaw.real {j | r ≤ max (h n) (j : ℝ)}) :
    (alternatingWord n).heightLaw.real {1} ≤
      (Forward.heightLaw RRT.allAttach n).real {j | j ≤ K} := by
  have htail := hdom (alternatingWord n) (alternatingWord_inFamily n) ((K : ℝ) + 1)
  have hclip : {j : ℕ | (K : ℝ) + 1 ≤ max (h n) (j : ℝ)} =
      {j : ℕ | (K : ℝ) + 1 ≤ (j : ℝ)} := by
    ext j
    simp only [Set.mem_ofPred_eq, le_max_iff]
    constructor
    · rintro (hh | hh)
      · linarith
      · exact hh
    · exact Or.inr
  have hcomp : {j : ℕ | (K : ℝ) + 1 ≤ (j : ℝ)} = {j : ℕ | j ≤ K}ᶜ := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · intro hh
      have hh' : K + 1 ≤ j := by exact_mod_cast hh
      omega
    · intro hh
      have hh' : K + 1 ≤ j := by omega
      exact_mod_cast hh'
  rw [hclip, hcomp, measureReal_compl (by trivial), measureReal_compl (by trivial),
    probReal_univ, probReal_univ] at htail
  have hstar : (alternatingWord n).heightLaw.real {1} ≤
      (alternatingWord n).heightLaw.real {j | j ≤ K} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro j hj
    have hj' : j = 1 := by simpa only [Set.mem_singleton_iff] using hj
    simpa only [Set.mem_ofPred_eq, hj'] using hK
  linarith

theorem question2_threshold_divergence : Question2ThresholdDivergenceClaim := by
  intro h hdom
  have hnat (K : ℕ) (hK : 1 ≤ K) : ∀ᶠ n : ℕ in atTop, (K : ℝ) < h n := by
    filter_upwards [eventually_rrt_boundedHeight_lt_alternating_star K,
      eventually_ge_atTop 1] with n hsmall hn
    by_contra hcut
    have hh := clipped_tail_comparison_forces_cdf hK (le_of_not_gt hcut) (hdom n hn)
    exact (not_le_of_gt hsmall) hh
  apply tendsto_atTop.mpr
  intro A
  let K : ℕ := max (Nat.ceil A) 1
  have hK : 1 ≤ K := le_max_right _ _
  have hAK : A ≤ (K : ℝ) := by
    have hh : (Nat.ceil A : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (le_max_left (Nat.ceil A) 1)
    exact (Nat.le_ceil A).trans hh
  filter_upwards [hnat K hK] with n hn
  exact hAK.trans hn.le

end FreezingGrowth
