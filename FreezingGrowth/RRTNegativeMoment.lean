module

public import FreezingGrowth.RRTSplitIntegrals
public import FreezingGrowth.LargerComponentSum
public import FreezingGrowth.HalfHarmonic

/-! A negative height moment bounded using the larger first-edge component. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory Filter
open scoped Topology

noncomputable def negativeBase : ℝ := 3 / 7

noncomputable def negativeMoment (n : ℕ) : ℝ :=
  ∫ s, negativeBase ^ Forward.treeHeight s ∂Forward.treeLaw allAttach n

theorem negativeMoment_nonneg (n : ℕ) : 0 ≤ negativeMoment n :=
  integral_nonneg (fun _ => pow_nonneg (by norm_num [negativeBase]) _)

theorem negativeMoment_le_one (n : ℕ) : negativeMoment n ≤ 1 := by
  calc
    _ ≤ ∫ _s, (1 : ℝ) ∂Forward.treeLaw allAttach n := integral_mono
      (Forward.treeLaw_integrable_heightTest allAttach n (fun k => negativeBase ^ k))
      (integrable_const _) (fun _ => pow_le_one₀ (by norm_num [negativeBase])
        (by norm_num [negativeBase]))
    _ = 1 := by simp

noncomputable def splitMomentTest (p : Forward.State × Forward.State) : ℝ :=
  negativeBase ^ max (Forward.treeHeight p.1) (Forward.treeHeight p.2 + 1)

theorem measurable_splitMomentTest : Measurable splitMomentTest :=
  (measurable_of_countable (fun p : ℕ × ℕ => negativeBase ^ max p.1 (p.2 + 1))).comp
    RRTSplit.measurable_heightPair

theorem splitMomentTest_integrable (k l : ℕ) : Integrable splitMomentTest
    ((Forward.treeLaw allAttach k).prod (Forward.treeLaw allAttach l)) := by
  apply (integrable_const (1 : ℝ)).mono' measurable_splitMomentTest.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by norm_num [negativeBase]) _)]
  exact pow_le_one₀ (by norm_num [negativeBase]) (by norm_num [negativeBase])

theorem integral_prod_left_negativeMoment (k l : ℕ) :
    (∫ p, negativeBase ^ Forward.treeHeight p.1
      ∂(Forward.treeLaw allAttach k).prod (Forward.treeLaw allAttach l)) = negativeMoment k := by
  rw [← integral_map (f := fun s : Forward.State => negativeBase ^ Forward.treeHeight s)
    measurable_fst.aemeasurable measurable_from_top.aestronglyMeasurable]
  simp [negativeMoment]

theorem integral_prod_right_negativeMoment (k l : ℕ) :
    (∫ p, negativeBase ^ Forward.treeHeight p.2
      ∂(Forward.treeLaw allAttach k).prod (Forward.treeLaw allAttach l)) = negativeMoment l := by
  rw [← integral_map (f := fun s : Forward.State => negativeBase ^ Forward.treeHeight s)
    measurable_snd.aemeasurable measurable_from_top.aestronglyMeasurable]
  simp [negativeMoment]

theorem splitMomentTest_integral_le (k l : ℕ) :
    (∫ p, splitMomentTest p
      ∂(Forward.treeLaw allAttach k).prod (Forward.treeLaw allAttach l)) ≤
        if l ≤ k then negativeMoment k else negativeBase * negativeMoment l := by
  have hiL : Integrable (fun p : Forward.State × Forward.State =>
      negativeBase ^ Forward.treeHeight p.1)
      ((Forward.treeLaw allAttach k).prod (Forward.treeLaw allAttach l)) := by
    apply (integrable_map_measure (g := fun s : Forward.State => negativeBase ^ Forward.treeHeight s)
      measurable_from_top.aestronglyMeasurable
      measurable_fst.aemeasurable).mp
    simpa using Forward.treeLaw_integrable_heightTest allAttach k (fun h => negativeBase ^ h)
  have hiR : Integrable (fun p : Forward.State × Forward.State =>
      negativeBase ^ Forward.treeHeight p.2)
      ((Forward.treeLaw allAttach k).prod (Forward.treeLaw allAttach l)) := by
    apply (integrable_map_measure (g := fun s : Forward.State => negativeBase ^ Forward.treeHeight s)
      measurable_from_top.aestronglyMeasurable
      measurable_snd.aemeasurable).mp
    simpa using Forward.treeLaw_integrable_heightTest allAttach l (fun h => negativeBase ^ h)
  split_ifs
  · rw [← integral_prod_left_negativeMoment k l]
    apply integral_mono (splitMomentTest_integrable k l) hiL
    intro p
    exact pow_le_pow_of_le_one (by norm_num [negativeBase])
      (by norm_num [negativeBase]) (le_max_left _ _)
  · rw [← integral_prod_right_negativeMoment k l, ← integral_const_mul]
    apply integral_mono (splitMomentTest_integrable k l) (hiR.const_mul _)
    intro p
    dsimp only
    rw [show negativeBase * negativeBase ^ Forward.treeHeight p.2 =
      negativeBase ^ (Forward.treeHeight p.2 + 1) by rw [pow_succ]; ring]
    exact pow_le_pow_of_le_one (by norm_num [negativeBase])
      (by norm_num [negativeBase]) (le_max_right _ _)

theorem negativeMoment_succ_le (n : ℕ) :
    (n + 1 : ℝ) * negativeMoment (n + 1) ≤
      (10 / 7 : ℝ) * ∑ j ∈ Finset.Ico ((n + 1) / 2) (n + 1), negativeMoment j := by
  have he : negativeMoment (n + 1) = ∫ p, splitMomentTest p ∂RRTSplit.pairLaw n := by
    rw [RRTSplit.pairLaw, integral_map measurable_from_top.aemeasurable
      measurable_splitMomentTest.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [RRTSplit.treeLaw_height_split n] with s hs
    exact congrArg (fun k => negativeBase ^ k) hs
  rw [he, RRTSplit.pairLaw_eq_sum, integral_smul_measure,
    integral_finsetSum_measure (fun k _ => splitMomentTest_integrable k (n - k))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        if n - k ≤ k then negativeMoment k else negativeBase * negativeMoment (n - k) :=
      Finset.sum_le_sum (fun k _ => splitMomentTest_integral_le k (n - k))
    _ ≤ _ := by
      simpa only [Nat.add_sub_cancel, negativeBase, show (1 : ℝ) + 3 / 7 = 10 / 7 by norm_num] using
        sum_larger_component_le (n + 1) negativeMoment negativeMoment_nonneg negativeBase
          (by norm_num [negativeBase])

end FreezingGrowth.RRT
