module

public import FreezingGrowth.RRTMeanDepthVariance
public import FreezingGrowth.ForwardPairAveraging
public import FreezingGrowth.ReverseUniformRootPair

/-! Divergence of the actual two-vertex absolute depth gap. The pair is sampled
uniformly inside the same random recursive tree. The argument uses marginal
moments and the bounded fluctuation of the tree mean, without a joint CLT. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory Filter
open scoped Classical Topology

noncomputable def treeDepthPairGap (s : Forward.State) : ℝ :=
  FiniteAveraging.pairSum s.active
    (fun u v => |(s.height u : ℝ) - s.height v|) / (s.active.card : ℝ) ^ 2

/-- Ordered distinct vertices; different vertices at equal depth still occur,
with their correct zero contribution. -/
noncomputable def treeDistinctDepthGap (s : Forward.State) : ℝ :=
  Forward.activeDistinctPairMean s (fun a b => |(a : ℝ) - b|)

noncomputable def expectedDepthPairGap (n : ℕ) : ℝ :=
  ∫ s, treeDepthPairGap s ∂Forward.treeLaw allAttach n

noncomputable def expectedDistinctDepthGap (n : ℕ) : ℝ :=
  ∫ s, treeDistinctDepthGap s ∂Forward.treeLaw allAttach n

/-- Both vertex choices are made in this same tree, conditionally independently. -/
theorem treeDepthPairGap_eq_integral (s : Forward.State) (hs : s.active.Nonempty) :
    treeDepthPairGap s = ∫ u, (∫ v, |(s.height u : ℝ) - s.height v|
      ∂Measure.uniformOfFinset s.active) ∂Measure.uniformOfFinset s.active := by
  simp_rw [Forward.integral_uniform_active s hs]
  rw [← Finset.sum_div]
  unfold treeDepthPairGap FiniteAveraging.pairSum
  rw [div_div, pow_two]

theorem treeDistinctDepthGap_eq_offDiag (s : Forward.State) (hs : 2 ≤ s.active.card) :
    treeDistinctDepthGap s =
      (∑ p ∈ s.active.offDiag, |(s.height p.1 : ℝ) - s.height p.2|) /
        (s.active.offDiag.card : ℝ) := by
  have he : s.active.offDiag =
      (s.active ×ˢ s.active).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsum : (∑ p ∈ s.active.offDiag, |(s.height p.1 : ℝ) - s.height p.2|) =
      FiniteAveraging.pairSum s.active
        (fun u v => |(s.height u : ℝ) - s.height v|) := by
    rw [he, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u = v
    · subst v
      simp
    · simp [huv]
  rw [hsum, card_offDiag_real s.active (by omega)]
  rfl

/-- The displayed statistic is exactly the uniform ordered sample without
replacement, not a pair of independent random trees. -/
theorem treeDistinctDepthGap_eq_integral (s : Forward.State) (hs : 2 ≤ s.active.card) :
    treeDistinctDepthGap s =
      ∫ p, |(s.height p.1 : ℝ) - s.height p.2| ∂uniformRootPair s.active := by
  rw [treeDistinctDepthGap_eq_offDiag s hs]
  unfold uniformRootPair Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro p _
    apply Integrable.smul_measure (integrable_dirac (by simp))
    exact ENNReal.inv_ne_top.mpr (by
      exact_mod_cast (offDiag_nonempty_of_two_le_card hs).card_pos.ne')

private theorem finite_mean_abs_le_pair_add {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ) (a : ℝ) :
    (∑ u ∈ s, |f u - a|) / s.card ≤
      FiniteAveraging.pairSum s (fun u v => |f u - f v|) / (s.card : ℝ) ^ 2 +
        |(∑ v ∈ s, f v) / s.card - a| := by
  let N : ℝ := s.card
  let M : ℝ := (∑ v ∈ s, f v) / N
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hs.card_pos
  have hrow (u : ι) : |f u - M| ≤ (∑ v ∈ s, |f u - f v|) / N := by
    have he : f u - M = (∑ v ∈ s, (f u - f v)) / N := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      dsimp [M, N]
      field_simp
    rw [he, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hN.le
  have hpoint (u : ι) : |f u - a| ≤ (∑ v ∈ s, |f u - f v|) / N + |M - a| := by
    have htri : |f u - a| ≤ |f u - M| + |M - a| := by
      have hh := abs_add_le (f u - M) (M - a)
      simpa only [sub_add_sub_cancel] using hh
    exact htri.trans (add_le_add (hrow u) (le_refl _))
  have hh := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun u (_ : u ∈ s) => hpoint u)) hN.le
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul] at hh
  change (∑ u ∈ s, |f u - a|) / N ≤ _
  convert hh using 1
  dsimp [FiniteAveraging.pairSum, N, M]
  field_simp

theorem activeMean_abs_sub_le_pairGap (s : Forward.State)
    (hs : s.active.Nonempty) (a : ℝ) :
    Forward.activeMean s (fun k => |(k : ℝ) - a|) ≤
      treeDepthPairGap s + |treeDepthMean s - a| :=
  finite_mean_abs_le_pair_add s.active hs (fun v => (s.height v : ℝ)) a

private theorem pairSum_nonneg (s : Forward.State) :
    0 ≤ FiniteAveraging.pairSum s.active (fun u v => |(s.height u : ℝ) - s.height v|) :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem treeDepthPairGap_nonneg (s : Forward.State) : 0 ≤ treeDepthPairGap s :=
  div_nonneg (pairSum_nonneg s) (sq_nonneg _)

theorem treeDistinctDepthGap_nonneg (s : Forward.State) : 0 ≤ treeDistinctDepthGap s := by
  by_cases hs : 2 ≤ s.active.card
  · have hN : (2 : ℝ) ≤ s.active.card := by exact_mod_cast hs
    exact div_nonneg (pairSum_nonneg s) (by nlinarith)
  · have hcard : s.active.card = 0 ∨ s.active.card = 1 := by omega
    rcases hcard with hcard | hcard <;>
      simp [treeDistinctDepthGap, Forward.activeDistinctPairMean,
        FiniteAveraging.distinctPairMean, hcard]

theorem treeDepthPairGap_le_distinct (s : Forward.State) (hs : 2 ≤ s.active.card) :
    treeDepthPairGap s ≤ treeDistinctDepthGap s := by
  have hN : (2 : ℝ) ≤ s.active.card := by exact_mod_cast hs
  unfold treeDepthPairGap treeDistinctDepthGap Forward.activeDistinctPairMean
    FiniteAveraging.distinctPairMean
  apply div_le_div_of_nonneg_left (pairSum_nonneg s) (by nlinarith)
  nlinarith

private theorem pairSum_bound {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s) :
    FiniteAveraging.pairSum s.active (fun u v => |(s.height u : ℝ) - s.height v|) ≤
      (s.active.card : ℝ) ^ 2 * (2 * n) := by
  have hp (u : ℕ) (hu : u ∈ s.active) : (s.height u : ℝ) ≤ n := by
    exact_mod_cast (hs.height_le_id u (hs.active_subset hu)).trans
      (hs.vertices_le u (hs.active_subset hu))
  have hh : FiniteAveraging.pairSum s.active
      (fun u v => |(s.height u : ℝ) - s.height v|) ≤
      ∑ _u ∈ s.active, ∑ _v ∈ s.active, (2 * (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    calc
      _ ≤ |(s.height u : ℝ)| + |(s.height v : ℝ)| := abs_sub _ _
      _ ≤ 2 * n := by
        rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
        linarith [hp u hu, hp v hv]
  simpa only [Finset.sum_const, nsmul_eq_mul, pow_two, mul_assoc] using hh

theorem treeDepthPairGap_bound {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s) :
    |treeDepthPairGap s| ≤ 2 * n := by
  rw [abs_of_nonneg (treeDepthPairGap_nonneg s)]
  by_cases hcard : s.active.card = 0
  · simp [treeDepthPairGap, hcard]
  · have hN : 0 < (s.active.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hcard
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    simpa only [mul_comm] using pairSum_bound hs

theorem treeDistinctDepthGap_bound {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s) :
    |treeDistinctDepthGap s| ≤ 4 * n := by
  rw [abs_of_nonneg (treeDistinctDepthGap_nonneg s)]
  by_cases hcard : 2 ≤ s.active.card
  · have hN : (2 : ℝ) ≤ s.active.card := by exact_mod_cast hcard
    change _ / ((s.active.card : ℝ) * ((s.active.card : ℝ) - 1)) ≤ _
    apply (div_le_iff₀ (by nlinarith : 0 <
      (s.active.card : ℝ) * ((s.active.card : ℝ) - 1))).mpr
    have hh := pairSum_bound hs
    have hmul := mul_nonneg (show 0 ≤ (s.active.card : ℝ) * ((s.active.card : ℝ) - 2)
      by nlinarith) (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  · have hh : s.active.card = 0 ∨ s.active.card = 1 := by omega
    rcases hh with hh | hh <;>
      simp [treeDistinctDepthGap, Forward.activeDistinctPairMean,
        FiniteAveraging.distinctPairMean, hh]

theorem treeDepthPairGap_integrable (n : ℕ) :
    Integrable treeDepthPairGap (Forward.treeLaw allAttach n) := by
  apply (integrable_const (2 * (n : ℝ))).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [Forward.treeLaw_valid allAttach n] with s hs
  simpa only [Real.norm_eq_abs] using treeDepthPairGap_bound hs

theorem treeDistinctDepthGap_integrable (n : ℕ) :
    Integrable treeDistinctDepthGap (Forward.treeLaw allAttach n) := by
  apply (integrable_const (4 * (n : ℝ))).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [Forward.treeLaw_valid allAttach n] with s hs
  simpa only [Real.norm_eq_abs] using treeDistinctDepthGap_bound hs

theorem uniformVertexDepthLaw_abs_centered_lower (n : ℕ) (hn : 1 ≤ depthMean n) :
    Real.sqrt (depthMean n) / 16 ≤
      ∫ k : ℕ, |(k : ℝ) - depthMean n| ∂uniformVertexDepthLaw n :=
  sqrt_le_integral_abs_of_moments
    (Forward.uniformActiveHeightLaw_integrable allAttach n _)
    (depthCenteredMoment_integrable n 2) (depthCenteredMoment_integrable n 4) hn
    (depthCenteredMoment_two_ge_half_mean n) (depthCenteredMoment_four_le_mean n)

theorem expectedDepthPairGap_lower (n : ℕ) (hn : 1 ≤ depthMean n) :
    Real.sqrt (depthMean n) / 16 - 1 ≤ expectedDepthPairGap n := by
  have hmean : Integrable (fun s => |treeDepthMean s - depthMean n|)
      (Forward.treeLaw allAttach n) := by
    simpa only [pow_one] using (integrable_treeMean_power n (depthMean n) 1).abs
  have hJ : (∫ s, Forward.activeMean s (fun k => |(k : ℝ) - depthMean n|)
      ∂Forward.treeLaw allAttach n) ≤ expectedDepthPairGap n +
        ∫ s, |treeDepthMean s - depthMean n| ∂Forward.treeLaw allAttach n := by
    change _ ≤ (∫ s, treeDepthPairGap s ∂Forward.treeLaw allAttach n) + _
    rw [← integral_add (treeDepthPairGap_integrable n) hmean]
    apply integral_mono_ae (Forward.treeLaw_integrable_activeMean allAttach n _)
      ((treeDepthPairGap_integrable n).add hmean)
    filter_upwards [Forward.treeLaw_active_nonempty allAttach n (before_extinction n)] with s hs
    exact activeMean_abs_sub_le_pairGap s hs (depthMean n)
  have hm := Forward.uniformActiveHeightLaw_integral allAttach n (before_extinction n)
    (fun k => |(k : ℝ) - depthMean n|)
  have hl := uniformVertexDepthLaw_abs_centered_lower n hn
  rw [uniformVertexDepthLaw, hm] at hl
  linarith [integral_abs_treeDepthMean_sub_mean_le_one n]

theorem expectedDepthPairGap_le_distinct (n : ℕ) (hn : 1 ≤ n) :
    expectedDepthPairGap n ≤ expectedDistinctDepthGap n := by
  apply integral_mono_ae (treeDepthPairGap_integrable n) (treeDistinctDepthGap_integrable n)
  filter_upwards [Forward.treeLaw_counts allAttach n (before_extinction n).le] with s hs
  have hc : (s.active.card : ℤ) = (n : ℤ) + 1 := by
    simpa only [activeCount_allAttach] using hs.1
  exact treeDepthPairGap_le_distinct s (by omega)

theorem expectedDistinctDepthGap_lower (n : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ depthMean n) :
    Real.sqrt (depthMean n) / 16 - 1 ≤ expectedDistinctDepthGap n :=
  (expectedDepthPairGap_lower n hm).trans (expectedDepthPairGap_le_distinct n hn)

theorem tendsto_expectedDepthPairGap_atTop : Tendsto expectedDepthPairGap atTop atTop := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt (depthMean n) / 16 - 1) atTop atTop := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ)
      ((Real.tendsto_sqrt_atTop.comp tendsto_depthMean_atTop).atTop_div_const
        (by norm_num : (0 : ℝ) < 16))
  apply tendsto_atTop_mono' _ _ hs
  filter_upwards [eventually_one_le_depthMean] with n hn
  exact expectedDepthPairGap_lower n hn

theorem tendsto_expectedDistinctDepthGap_atTop :
    Tendsto expectedDistinctDepthGap atTop atTop := by
  apply tendsto_atTop_mono' _ _ tendsto_expectedDepthPairGap_atTop
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact expectedDepthPairGap_le_distinct n hn

end FreezingGrowth.RRT
