module

public import FreezingGrowth.TwoSeedHeightModel
public import FreezingGrowth.RRTSplitResidualDecay
public import FreezingGrowth.PaperPrefixSize

/-!
# The two source remainders on the actual joint height model

The old ordered depths and maximum have their genuine same-tree law. Fresh
component heights have the actual first-edge split law. These are the source
`Z` and `hat Z` positive parts, including the child-first orientation of `Z`.
-/

@[expose] public section

namespace FreezingGrowth.TwoSeedCoupling

open MeasureTheory Filter
open scoped Classical Topology

def sourceZ (z : ModelSample) : ℝ :=
  (z.1.2.2 : ℝ) - max ((z.1.1 : ℝ) + 1 + z.2.1) ((z.1.1 : ℝ) + z.2.2)

def sourceHatZ (z : ModelSample) : ℝ :=
  (z.1.2.2 : ℝ) - max ((z.1.1 : ℝ) + z.2.1) ((z.1.2.1 : ℝ) + z.2.2)

def sourceZPositive (z : ModelSample) : ℝ := max (sourceZ z) 0

def sourceHatZPositive (z : ModelSample) : ℝ := max (sourceHatZ z) 0

def commonRemainder (z : ModelSample) : ℝ :=
  max ((z.1.2.2 : ℝ) - (max z.2.1 z.2.2 : ℕ)) 0

theorem sourceZPositive_nonneg (z : ModelSample) : 0 ≤ sourceZPositive z := le_max_right _ _

theorem sourceHatZPositive_nonneg (z : ModelSample) : 0 ≤ sourceHatZPositive z := le_max_right _ _

theorem sourceZPositive_le_common (z : ModelSample) : sourceZPositive z ≤ commonRemainder z := by
  unfold sourceZPositive sourceZ commonRemainder
  apply max_le_max _ le_rfl
  apply sub_le_sub_left
  rw [Nat.cast_max]
  apply max_le_max <;> have := Nat.cast_nonneg (α := ℝ) z.1.1 <;> linarith

theorem sourceHatZPositive_le_common (z : ModelSample) : sourceHatZPositive z ≤ commonRemainder z := by
  unfold sourceHatZPositive sourceHatZ commonRemainder
  apply max_le_max _ le_rfl
  apply sub_le_sub_left
  rw [Nat.cast_max]
  apply max_le_max
  · have := Nat.cast_nonneg (α := ℝ) z.1.1
    linarith
  · have := Nat.cast_nonneg (α := ℝ) z.1.2.1
    linarith

def maximumAndSplit (z : ModelSample) : ℕ × (ℕ × ℕ) := (z.1.2.2, z.2)

theorem heightModelLaw_maximumAndSplit (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (heightModelLaw m n).map maximumAndSplit = RRTSplit.oldSplitHeightLaw m n := by
  have hh := Measure.map_prod_map (depthMaximumLaw m) (RRTSplit.heightPairLaw n)
    (f := fun d : DepthMaximum => d.2.2) (g := id) (measurable_of_countable _) measurable_id
  rw [depthMaximumLaw_maximum m hm, Measure.map_id] at hh
  exact hh.symm

theorem integral_commonRemainder (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∫ z, commonRemainder z ∂heightModelLaw m n) = RRTSplit.residual m n := by
  rw [RRTSplit.residual, ← heightModelLaw_maximumAndSplit m hm n,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  rfl

noncomputable def meanZPositive (m n : ℕ) : ℝ :=
  ∫ z, sourceZPositive z ∂heightModelLaw m n

noncomputable def meanHatZPositive (m n : ℕ) : ℝ :=
  ∫ z, sourceHatZPositive z ∂heightModelLaw m n

theorem meanZPositive_nonneg (m n : ℕ) : 0 ≤ meanZPositive m n :=
  integral_nonneg sourceZPositive_nonneg

theorem meanHatZPositive_nonneg (m n : ℕ) : 0 ≤ meanHatZPositive m n :=
  integral_nonneg sourceHatZPositive_nonneg

theorem meanZPositive_le_residual (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    meanZPositive m n ≤ RRTSplit.residual m n := by
  rw [← integral_commonRemainder m hm n]
  exact integral_mono (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _)
    sourceZPositive_le_common

theorem meanHatZPositive_le_residual (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    meanHatZPositive m n ≤ RRTSplit.residual m n := by
  rw [← integral_commonRemainder m hm n]
  exact integral_mono (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _)
    sourceHatZPositive_le_common

theorem tendsto_remainder_of_le_residual (f : ℕ → ℕ → ℝ) (hf : ∀ m n, 0 ≤ f m n)
    (hbound : ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, f m n ≤ RRTSplit.residual m n) :
    Tendsto (fun n : ℕ => f (paperPrefixSize n) n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hf _ _))
  · intro b hb
    have he := tendsto_paperPrefixSize_atTop.eventually
      (RRTSplit.residual_uniform_tendsto_zero (b / 2) (half_pos hb))
    filter_upwards [he, tendsto_paperPrefixSize_atTop.eventually_ge_atTop 1] with n hn hm
    exact (hbound _ hm n).trans_lt ((hn n (paperPrefixSize_pow_nine_le n)).trans_lt (half_lt_self hb))

theorem tendsto_meanZPositive_paperPrefix :
    Tendsto (fun n : ℕ => meanZPositive (paperPrefixSize n) n) atTop (𝓝 0) :=
  tendsto_remainder_of_le_residual meanZPositive meanZPositive_nonneg meanZPositive_le_residual

theorem tendsto_meanHatZPositive_paperPrefix :
    Tendsto (fun n : ℕ => meanHatZPositive (paperPrefixSize n) n) atTop (𝓝 0) :=
  tendsto_remainder_of_le_residual meanHatZPositive meanHatZPositive_nonneg meanHatZPositive_le_residual

noncomputable def comparisonLaw (m n : ℕ) : Measure (ℕ × ℕ) :=
  (Forward.heightLaw RRT.allAttach m).prod (Forward.heightLaw RRT.allAttach (n / 2))

instance comparisonLaw_probability (m n : ℕ) : IsProbabilityMeasure (comparisonLaw m n) :=
  inferInstanceAs (IsProbabilityMeasure ((Forward.heightLaw RRT.allAttach m).prod
    (Forward.heightLaw RRT.allAttach (n / 2))))

def comparisonBound (m : ℕ) (p : ℕ × ℕ) : ℝ := if p.2 ≤ p.1 then (m : ℝ) else 0

theorem comparisonBound_nonneg (m : ℕ) (p : ℕ × ℕ) : 0 ≤ comparisonBound m p := by
  unfold comparisonBound
  split_ifs <;> positivity

theorem heightModelLaw_ae_maximum_le (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ∀ᵐ z ∂heightModelLaw m n, z.1.2.2 ≤ m := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [depthMaximumLaw_ae_valid m hm] with d hd
  exact Eventually.of_forall (fun _ => hd.2)

theorem commonRemainder_le_maximum (z : ModelSample) : commonRemainder z ≤ (z.1.2.2 : ℝ) := by
  unfold commonRemainder
  apply max_le
  · have := Nat.cast_nonneg (α := ℝ) (max z.2.1 z.2.2)
    linarith
  · exact Nat.cast_nonneg _

theorem real_prod_event_eq_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (α × β)) (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∫ a, ν.real {b | (a, b) ∈ E} ∂μ := by
  rw [← integral_indicator_one hE]
  change (∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) = _
  rw [integral_prod (E.indicator (fun _ => (1 : ℝ)))
    ((integrable_const (1 : ℝ)).indicator hE)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun a => by
    change (∫ b, {b | (a, b) ∈ E}.indicator (fun _ => (1 : ℝ)) b ∂ν) = _
    exact integral_indicator_one (hE.preimage measurable_prodMk_left))

theorem heightModelLaw_positive_common_le_comparison (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (heightModelLaw m n).real {z | (max z.2.1 z.2.2 : ℕ) < z.1.2.2} ≤
      (comparisonLaw m n).real {p | p.2 ≤ p.1} := by
  let := heightModelLaw_probability m hm n
  have he : (heightModelLaw m n).real {z | (max z.2.1 z.2.2 : ℕ) < z.1.2.2} =
      (RRTSplit.oldSplitHeightLaw m n).real {p | max p.2.1 p.2.2 < p.1} := by
    rw [← heightModelLaw_maximumAndSplit m hm n,
      map_measureReal_apply (measurable_of_countable _) (by measurability)]
    rfl
  rw [he, RRTSplit.oldSplitHeightLaw, comparisonLaw,
    real_prod_event_eq_integral _ _ _ (by measurability),
    real_prod_event_eq_integral _ _ _ (by measurability)]
  apply integral_mono (Forward.heightLaw_integrable RRT.allAttach m _)
    (Forward.heightLaw_integrable RRT.allAttach m _)
  intro h
  have hsplit := RRTSplit.heightPairLaw_max_lowerTail_le n (h : ℝ)
  have hsplit' : (RRTSplit.heightPairLaw n).real {p | max p.1 p.2 < h} ≤
      RRT.lowerTail (n / 2) (h : ℝ) := by
    simpa only [Nat.cast_lt] using hsplit
  apply hsplit'.trans
  apply measureReal_mono (μ := Forward.heightLaw RRT.allAttach (n / 2)) ?_ (measure_ne_top _ _)
  intro k hk
  change (k : ℝ) < (h : ℝ) at hk
  exact (Nat.cast_lt.mp hk).le

/-- The source's binary stochastic dominator, tested at every real strict
threshold. The comparison trees are independent and have their actual laws. -/
theorem remainder_strict_tail_le_comparison (f : ModelSample → ℝ)
    (hf : ∀ z, 0 ≤ f z) (hle : ∀ z, f z ≤ commonRemainder z)
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (r : ℝ) :
    (heightModelLaw m n).real {z | r < f z} ≤
      (comparisonLaw m n).real {p | r < comparisonBound m p} := by
  let := heightModelLaw_probability m hm n
  by_cases hr : r < 0
  · have hleft : {z : ModelSample | r < f z} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hr.trans_le (hf z)
    have hright : {p : ℕ × ℕ | r < comparisonBound m p} = Set.univ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hr.trans_le (comparisonBound_nonneg m p)
    simpa only [hleft, hright, probReal_univ] using (le_refl (1 : ℝ))
  · have hr0 : 0 ≤ r := le_of_not_gt hr
    by_cases hrm : r < (m : ℝ)
    · have hsub : {z : ModelSample | r < f z} ⊆
          {z | max z.2.1 z.2.2 < z.1.2.2} := by
        intro z hz
        have hpos : 0 < commonRemainder z := (hr0.trans_lt hz).trans_le (hle z)
        have hd : 0 < (z.1.2.2 : ℝ) - (max z.2.1 z.2.2 : ℕ) :=
          (lt_max_iff.mp hpos).resolve_right (by simp)
        exact_mod_cast (sub_pos.mp hd)
      have hright : {p : ℕ × ℕ | r < comparisonBound m p} = {p | p.2 ≤ p.1} := by
        ext p
        by_cases hp : p.2 ≤ p.1
        · simp [comparisonBound, hp, hrm]
        · simp [comparisonBound, hp, not_lt.mpr hr0]
      rw [hright]
      exact (measureReal_mono hsub).trans (heightModelLaw_positive_common_le_comparison m hm n)
    · have hzero : (heightModelLaw m n).real {z | r < f z} = 0 := by
        rw [← integral_indicator_one (by measurability : MeasurableSet {z | r < f z})]
        apply integral_eq_zero_of_ae
        filter_upwards [heightModelLaw_ae_maximum_le m hm n] with z hz
        have hbound : f z ≤ (m : ℝ) :=
          ((hle z).trans (commonRemainder_le_maximum z)).trans (Nat.cast_le.mpr hz)
        have hnot : z ∉ {z | r < f z} := by
          change ¬r < f z
          linarith
        exact Set.indicator_of_notMem hnot _
      rw [hzero]
      exact measureReal_nonneg

theorem sourceZPositive_strict_tail_le_comparison (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (r : ℝ) :
    (heightModelLaw m n).real {z | r < sourceZPositive z} ≤
      (comparisonLaw m n).real {p | r < comparisonBound m p} :=
  remainder_strict_tail_le_comparison sourceZPositive sourceZPositive_nonneg
    sourceZPositive_le_common m hm n r

theorem sourceHatZPositive_strict_tail_le_comparison (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (r : ℝ) :
    (heightModelLaw m n).real {z | r < sourceHatZPositive z} ≤
      (comparisonLaw m n).real {p | r < comparisonBound m p} :=
  remainder_strict_tail_le_comparison sourceHatZPositive sourceHatZPositive_nonneg
    sourceHatZPositive_le_common m hm n r

end FreezingGrowth.TwoSeedCoupling
