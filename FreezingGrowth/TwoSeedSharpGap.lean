module

public import FreezingGrowth.RRTSharpSplitMean
public import FreezingGrowth.TwoSeedHeightDecomposition
public import FreezingGrowth.FreezeAttachGap

/-! The source's bounded comparison error, on the genuine same-tree depth
law and independent actual component-height split. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedCoupling

open MeasureTheory Filter
open scoped Topology

theorem integral_heightModel_depth (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (F : DepthMaximum → ℝ) :
    (∫ z, F z.1 ∂heightModelLaw m n) = ∫ d, F d ∂depthMaximumLaw m := by
  rw [heightModelLaw_integral m hm n]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem integral_heightModel_split (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (F : ℕ × ℕ → ℝ) :
    (∫ z, F z.2 ∂heightModelLaw m n) = ∫ p, F p ∂RRTSplit.heightPairLaw n := by
  let := depthMaximumLaw_probability m hm
  rw [heightModelLaw_integral m hm n]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem integral_depthMaximum_absolute_gap (m : ℕ) (hm : 1 ≤ m) :
    (∫ d : DepthMaximum, |(d.2.1 : ℝ) - d.1| ∂depthMaximumLaw m) =
      RRT.expectedDistinctDepthGap m := by
  rw [depthMaximumLaw_integral m hm]
  apply integral_congr_ae
  filter_upwards [Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs
  have hc : (s.active.card : ℤ) = (m : ℤ) + 1 := by
    simpa only [RRT.activeCount_allAttach] using hs.1
  have hcard : 2 ≤ s.active.card := by omega
  change Forward.activePairHeightMean s (fun a b (_ : ℕ) => |(b : ℝ) - a|) = _
  have he : (fun (a b : ℕ) (_ : ℕ) => |(b : ℝ) - a|) =
      (fun (a b : ℕ) (_ : ℕ) => |(a : ℝ) - b|) := by
    funext a b M
    exact abs_sub_comm _ _
  rw [he]
  exact Forward.activePairHeightMean_depth_gap s hcard

/-- Exchangeability is within the same original RRT, with distinct vertices. -/
theorem integral_depthMaximum_positive_gap (m : ℕ) (hm : 1 ≤ m) :
    (∫ d : DepthMaximum, max 0 ((d.2.1 : ℝ) - d.1) ∂depthMaximumLaw m) =
      RRT.expectedDistinctDepthGap m / 2 := by
  let F : DepthMaximum → ℝ := fun d => max 0 ((d.2.1 : ℝ) - d.1)
  have hswap := integral_map (μ := depthMaximumLaw m) (f := F)
    (measurable_of_countable swapDepthMaximum).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable
  rw [depthMaximumLaw_swap m hm] at hswap
  have hpoint (d : DepthMaximum) :
      F d + F (swapDepthMaximum d) = |(d.2.1 : ℝ) - d.1| := by
    simpa only [F, swapDepthMaximum, neg_sub] using
      positiveParts_sum_eq_abs ((d.2.1 : ℝ) - d.1)
  have he := integral_congr_ae (μ := depthMaximumLaw m)
    (Filter.Eventually.of_forall hpoint)
  rw [integral_add (depthMaximumLaw_integrable m hm F)
    (depthMaximumLaw_integrable m hm (fun d => F (swapDepthMaximum d))),
    integral_depthMaximum_absolute_gap m hm] at he
  change (∫ d, F d ∂depthMaximumLaw m) = _
  linarith

theorem freezeAttachExpectedGap_eq_model (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    freezeAttachExpectedGap m n =
      ∫ z, ((baselineHeight z : ℝ) - longHeight z) ∂heightModelLaw m n := by
  have hb := integral_map (μ := heightModelLaw m n) (f := fun h : ℕ => (h : ℝ))
    (measurable_of_countable baselineHeight).aemeasurable
    (measurable_of_countable (fun h : ℕ => (h : ℝ))).aestronglyMeasurable
  have hl := integral_map (μ := heightModelLaw m n) (f := fun h : ℕ => (h : ℝ))
    (measurable_of_countable longHeight).aemeasurable
    (measurable_of_countable (fun h : ℕ => (h : ℝ))).aestronglyMeasurable
  rw [baselineHeight_marginal m hm n] at hb
  rw [longHeight_marginal m hm n] at hl
  unfold freezeAttachExpectedGap Word.expectedHeight
  rw [hb, hl, integral_sub (heightModelLaw_integrable m hm n _)
    (heightModelLaw_integrable m hm n _)]

theorem source_gap_error_pointwise (z : ModelSample) :
    |((baselineHeight z : ℝ) - longHeight z) - max 0 ((z.1.2.1 : ℝ) - z.1.1)| ≤
      1 + 2 * |componentImbalance z| + sourceZPositive z + sourceHatZPositive z := by
  rw [sourceHatZ_height_decomposition, sourceZ_height_decomposition]
  have hp := positivePart_perturbation_bounds ((z.1.2.1 : ℝ) - z.1.1) (componentImbalance z)
  have hm : max 1 (componentImbalance z) ≤ 1 + |componentImbalance z| := by
    exact max_le (by have := abs_nonneg (componentImbalance z); linarith)
      (by have := le_abs_self (componentImbalance z); linarith)
  have hm0 : 0 ≤ max 1 (componentImbalance z) := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hz := sourceZPositive_nonneg z
  have hh := sourceHatZPositive_nonneg z
  apply abs_le.mpr
  constructor <;> linarith

/-- The quantitative form of the source's two bounded-error equalities. -/
theorem freezeAttachExpectedGap_absolute_error (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    |freezeAttachExpectedGap m n - RRT.expectedDistinctDepthGap m / 2| ≤
      1 + 2 * RRTSplit.roughHeightGap n + meanZPositive m n + meanHatZPositive m n := by
  let := heightModelLaw_probability m hm n
  let F : ModelSample → ℝ := fun z =>
    ((baselineHeight z : ℝ) - longHeight z) - max 0 ((z.1.2.1 : ℝ) - z.1.1)
  have he : (∫ z, F z ∂heightModelLaw m n) =
      freezeAttachExpectedGap m n - RRT.expectedDistinctDepthGap m / 2 := by
    rw [integral_sub (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _),
      ← freezeAttachExpectedGap_eq_model m hm n,
      integral_heightModel_depth m hm n (fun d => max 0 ((d.2.1 : ℝ) - d.1)),
      integral_depthMaximum_positive_gap m hm]
  have hbound := integral_mono (heightModelLaw_integrable m hm n (fun z => |F z|))
    (heightModelLaw_integrable m hm n (fun z =>
      1 + 2 * |componentImbalance z| + sourceZPositive z + sourceHatZPositive z))
    source_gap_error_pointwise
  have hi := abs_integral_le_integral_abs (μ := heightModelLaw m n) (f := F)
  rw [he] at hi
  apply (hi.trans hbound).trans_eq
  rw [integral_add (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _),
    integral_add (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _),
    integral_add (integrable_const 1) (heightModelLaw_integrable m hm n _),
    integral_const, integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [show (∫ z, |componentImbalance z| ∂heightModelLaw m n) = RRTSplit.roughHeightGap n by
    exact integral_heightModel_split m hm n (fun p => |(p.2 : ℝ) - p.1|) |>.trans (by
      unfold RRTSplit.roughHeightGap
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => abs_sub_comm _ _))]
  rfl

/-- I7 at the manuscript's full floor index, rather than a subsequence. -/
theorem freezeAttachExpectedGap_floor_bounded_error :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      |freezeAttachExpectedGap (paperPrefixSize n) n -
        RRT.expectedDistinctDepthGap (paperPrefixSize n) / 2| ≤ B := by
  obtain ⟨C, hC, hsplit⟩ := RRTSplit.uniformHeightGap
  refine ⟨3 + 2 * C, by positivity, ?_⟩
  have hz := tendsto_meanZPositive_paperPrefix.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hh := tendsto_meanHatZPositive_paperPrefix.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hz, hh, tendsto_paperPrefixSize_atTop.eventually_ge_atTop 1] with n hn hn' hm
  have he := freezeAttachExpectedGap_absolute_error (paperPrefixSize n) hm n
  have hs := hsplit n
  change meanZPositive (paperPrefixSize n) n < 1 at hn
  change meanHatZPositive (paperPrefixSize n) n < 1 at hn'
  linarith

end FreezingGrowth.TwoSeedCoupling
