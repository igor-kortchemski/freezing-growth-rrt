module

public import FreezingGrowth.RRTSplitSampling
public import FreezingGrowth.RRTSharpSplitMean
public import FreezingGrowth.PaperHeightComparison

/-! Sharp tails for the actual two recursive-tree component heights. The
source's two-exponential bound is retained before constants are combined. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory Set Filter
open scoped Topology Classical

namespace RRTSplit

theorem sampledHeightDeviation_le_of_uniform (n : ℕ) (t B : ℝ)
    (hB : ∀ i : ℕ, i ≤ n →
      (Forward.heightLaw RRT.allAttach i).real {h | t ≤ |(h : ℝ) - RRT.meanHeight i|} ≤ B) :
    sampledHeightDeviation n t ≤ B := by
  rw [sampledHeightDeviation_eq_sum]
  have hh := Finset.sum_le_sum (s := Finset.range (n + 1))
    (fun i hi => hB i (by have := Finset.mem_range.mp hi; omega))
  apply (mul_le_mul_of_nonneg_left hh (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity)).trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

noncomputable def marginalDeviationMaximum (n : ℕ) (t : ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩
    (fun i => (Forward.heightLaw RRT.allAttach i).real {h | t ≤ |(h : ℝ) - RRT.meanHeight i|})

theorem sampledHeightDeviation_le_maximum (n : ℕ) (t : ℝ) :
    sampledHeightDeviation n t ≤ marginalDeviationMaximum n t := by
  apply sampledHeightDeviation_le_of_uniform
  intro i hi
  exact Finset.le_sup' (f := fun i => (Forward.heightLaw RRT.allAttach i).real
    {h | t ≤ |(h : ℝ) - RRT.meanHeight i|}) (Finset.mem_range.mpr (by omega))

theorem uniformIndexLaw_real_mono_on_support (n : ℕ) (E F : Set ℕ)
    (hsub : ∀ i : ℕ, i ≤ n → i ∈ E → i ∈ F) :
    (uniformIndexLaw n).real E ≤ (uniformIndexLaw n).real F := by
  rw [uniformIndexLaw_real, uniformIndexLaw_real]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  have hh := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hh.1, hsub i (by have := Finset.mem_range.mp hh.1; omega) hh.2⟩

theorem sampledMeanDeviation_le_ratio_event {C : ℝ} (hC : 0 < C)
    (hmean : ∀ n i : ℕ, i ≤ n → |RRT.meanHeight n - RRT.meanHeight i| ≤
      -C * Real.log (((i : ℝ) + 1) / ((n : ℝ) + 1)) + C) (n : ℕ) (k : ℝ) :
    sampledMeanDeviation n (k / 4) ≤ (uniformIndexLaw n).real
      {i | ((i : ℝ) + 1) / ((n : ℝ) + 1) ≤ Real.exp (1 - k / (4 * C))} := by
  unfold sampledMeanDeviation
  apply uniformIndexLaw_real_mono_on_support
  intro i hin hi
  have hh := hmean n i hin
  change k / 4 ≤ |RRT.meanHeight i - RRT.meanHeight n| at hi
  rw [abs_sub_comm] at hi
  change ((i : ℝ) + 1) / ((n : ℝ) + 1) ≤ Real.exp (1 - k / (4 * C))
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  have he : C * (1 - k / (4 * C)) = C - k / 4 := by field_simp
  apply (mul_le_mul_iff_right₀ hC).mp
  rw [he]
  linarith

theorem sampledMeanDeviation_exp_le {C : ℝ} (hC : 0 < C)
    (hmean : ∀ n i : ℕ, i ≤ n → |RRT.meanHeight n - RRT.meanHeight i| ≤
      -C * Real.log (((i : ℝ) + 1) / ((n : ℝ) + 1)) + C) (n : ℕ) (k : ℝ) :
    sampledMeanDeviation n (k / 4) ≤ Real.exp (1 - k / (4 * C)) :=
  (sampledMeanDeviation_le_ratio_event hC hmean n k).trans
    (uniformIndexLaw_ratio_le n (Real.exp_pos _).le)

/-- The source's intermediate maximum-and-uniform-ratio inequality. -/
theorem heightPair_tail_le_maximum_and_ratio {C : ℝ} (hC : 0 < C)
    (hmean : ∀ n i : ℕ, i ≤ n → |RRT.meanHeight n - RRT.meanHeight i| ≤
      -C * Real.log (((i : ℝ) + 1) / ((n : ℝ) + 1)) + C) (n : ℕ) (k : ℝ) :
    (heightPairLaw n).real {p | k ≤ |(p.1 : ℝ) - (p.2 : ℝ)|} ≤
      2 * marginalDeviationMaximum n (k / 4) + 2 * (uniformIndexLaw n).real
        {i | ((i : ℝ) + 1) / ((n : ℝ) + 1) ≤ Real.exp (1 - k / (4 * C))} := by
  apply (heightPair_tail_le_sampled_deviations n k).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (sampledHeightDeviation_le_maximum n (k / 4)) (by norm_num))
    (mul_le_mul_of_nonneg_left (sampledMeanDeviation_le_ratio_event hC hmean n k) (by norm_num))

/-- LP4, with the two original exponential terms and their numerical rates. -/
theorem heightPair_two_exponential_tail :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, ∀ k : ℝ, 0 ≤ k →
      (heightPairLaw n).real {p | k ≤ |(p.1 : ℝ) - (p.2 : ℝ)|} ≤
        2 * c * Real.exp (-k / (12 * Real.exp 1)) + 2 * Real.exp (1 - k / (4 * C)) := by
  obtain ⟨c, hc, htail⟩ := RRT.meanCenteredHeightConcentration
  obtain ⟨C, hC, hmean⟩ := RRT.meanHeight_logarithmic_increment_ratio
  refine ⟨c, C, hc, hC, fun n k hk => ?_⟩
  have hdev := sampledHeightDeviation_le_of_uniform n (k / 4)
    (c * Real.exp (-(k / 4) / (3 * Real.exp 1)))
    (fun i _ => htail i (k / 4) (by positivity))
  have hmeans := sampledMeanDeviation_exp_le hC hmean n k
  have he : -(k / 4) / (3 * Real.exp 1) = -k / (12 * Real.exp 1) := by ring
  rw [he] at hdev
  exact (heightPair_tail_le_sampled_deviations n k).trans
    (by nlinarith)

theorem two_exponential_tail_absorption {c C c₁ : ℝ} (hc : 0 ≤ c) (_hC : 0 < C)
    (hc₁c : c ≤ c₁) (hc₁e : Real.exp 1 ≤ c₁) {k : ℝ} (hk : 0 ≤ k) :
    2 * c * Real.exp (-k / (12 * Real.exp 1)) + 2 * Real.exp (1 - k / (4 * C)) ≤
      4 * c₁ * Real.exp (-(min (1 / (3 * Real.exp 1)) (1 / C)) * k / 4) := by
  let c₂ := min (1 / (3 * Real.exp 1)) (1 / C)
  have hk4 : 0 ≤ k / 4 := by positivity
  have hrate₁ := mul_le_mul_of_nonneg_right (min_le_left (1 / (3 * Real.exp 1)) (1 / C)) hk4
  have hrate₂ := mul_le_mul_of_nonneg_right (min_le_right (1 / (3 * Real.exp 1)) (1 / C)) hk4
  have hpow₁ : Real.exp (-k / (12 * Real.exp 1)) ≤ Real.exp (-c₂ * k / 4) := by
    apply Real.exp_le_exp.mpr
    have he : -k / (12 * Real.exp 1) = -(1 / (3 * Real.exp 1) * (k / 4)) := by ring
    rw [he]
    rw [show -c₂ * k / 4 = -(c₂ * (k / 4)) by ring]
    exact neg_le_neg hrate₁
  have hpow₂ : Real.exp (-k / (4 * C)) ≤ Real.exp (-c₂ * k / 4) := by
    apply Real.exp_le_exp.mpr
    have he : -k / (4 * C) = -(1 / C * (k / 4)) := by ring
    rw [he]
    rw [show -c₂ * k / 4 = -(c₂ * (k / 4)) by ring]
    exact neg_le_neg hrate₂
  have h₁ := mul_le_mul hc₁c hpow₁ (Real.exp_pos _).le (hc.trans hc₁c)
  have h₂ := mul_le_mul hc₁e hpow₂ (Real.exp_pos _).le (hc.trans hc₁c)
  have he : Real.exp (1 - k / (4 * C)) = Real.exp 1 * Real.exp (-k / (4 * C)) := by
    rw [show 1 - k / (4 * C) = 1 + (-k / (4 * C)) by ring, Real.exp_add]
  rw [he]
  change 2 * c * Real.exp (-k / (12 * Real.exp 1)) +
    2 * (Real.exp 1 * Real.exp (-k / (4 * C))) ≤ 4 * c₁ * Real.exp (-c₂ * k / 4)
  nlinarith


end RRTSplit

/-- A common pair of constants for both assertions of source Lemma2.2. -/
theorem paper_height_comparison_and_split_tails :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ᶠ n : ℕ in atTop,
        (TwoSeedCoupling.comparisonLaw (paperPrefixSize n) n).real {p | p.2 ≤ p.1} ≤
          2 * c₁ * (n : ℝ) ^ (-(1 / 8 : ℝ))) ∧
      (∀ n : ℕ, ∀ k : ℝ, 0 ≤ k →
        (RRTSplit.heightPairLaw n).real {p | k ≤ |(p.1 : ℝ) - (p.2 : ℝ)|} ≤
          4 * c₁ * Real.exp (-c₂ * k / 4)) := by
  obtain ⟨cL, hcL, hL⟩ := paper_height_comparison_polynomial
  obtain ⟨c, C, hc, hC, htail⟩ := RRTSplit.heightPair_two_exponential_tail
  let c₁ := max cL (max c (Real.exp 1))
  let c₂ := min (1 / (3 * Real.exp 1)) (1 / C)
  have hc₁L : cL ≤ c₁ := le_max_left _ _
  have hc₁c : c ≤ c₁ := (le_max_left c (Real.exp 1)).trans (le_max_right _ _)
  have hc₁e : Real.exp 1 ≤ c₁ := (le_max_right c (Real.exp 1)).trans (le_max_right _ _)
  refine ⟨c₁, c₂, hcL.trans_le hc₁L, by dsimp [c₂]; positivity, ?_, ?_⟩
  · filter_upwards [hL] with n hn
    apply hn.trans
    gcongr
  · intro n k hk
    exact (htail n k hk).trans (RRTSplit.two_exponential_tail_absorption hc.le hC hc₁c hc₁e hk)

end FreezingGrowth
