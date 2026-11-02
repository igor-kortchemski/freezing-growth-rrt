module

public import FreezingGrowth.BernoulliConcentration
public import FreezingGrowth.ReverseFirstPairDeletion
public import FreezingGrowth.AlternatingStarProbability
public import FreezingGrowth.RRTSplitLaw
public import FreezingGrowth.Question3Bound
public import FreezingGrowth.RemoveAttachAnalytic
public import FreezingGrowth.RemovalEventually
public import FreezingGrowth.UniformHeightBounds
public import FreezingGrowth.MainDeletionClaims
public import FreezingGrowth.FloorDeletionGaps
public import FreezingGrowth.Question2Threshold

/-!
# Proved numbered results

Only results proved with their source hypotheses belong here. In particular,
the unproved Introduction targets in `MainStatements` are not theorem exports.
-/

@[expose] public section

namespace FreezingGrowth.Paper

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Theorem 1.2: the exact uniform probability and expectation conclusions
for every admissible attachment/freezing word, including terminal extinction.
The high-population proof uses the corrected prefix index `r - 1`. -/
theorem theorem_1_2 : UniformHeightProbabilityClaim ∧ UniformHeightExpectationClaim :=
  uniformHeightClaims

theorem theorem_1_2_probability : UniformHeightProbabilityClaim := uniformHeightProbabilityClaim

theorem theorem_1_2_expectation : UniformHeightExpectationClaim := uniformHeightExpectationClaim

/-- Proposition 3.1 (`prop:bennett`): both Bennett bounds for `n` independent
Bernoulli random variables, including endpoint parameters and every `t > 0`. -/
theorem bennett {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (n : ℕ) (Y : Fin n → Ω → ℝ) (p : Fin n → unitInterval)
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (hm : 0 < ∑ i, (p i : ℝ)) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | (∑ i, (p i : ℝ)) + t < ∑ i, Y i ω} ≤
      Real.exp (-(∑ i, (p i : ℝ)) * bennettRate (t / (∑ i, (p i : ℝ)))) ∧
    μ.real {ω | (∑ i, Y i ω) < (∑ i, (p i : ℝ)) - t} ≤
      Real.exp (-(∑ i, (p i : ℝ)) * bennettRate (t / (∑ i, (p i : ℝ)))) := by
  exact ⟨bernoulli_sum_upper_tail hY h_indep hLaw Finset.univ hm ht,
    bernoulli_sum_lower_tail hY h_indep hLaw Finset.univ hm ht⟩

/-- Theorem 1.3 (`prop:decreaseheight`): deleting the last attachment of the
initial run together with the first freeze gives a valid sequence whose actual
height is stochastically dominated by the original, including `k = 1` and
terminal extinction. The proof is a terminal-law reformulation through the
actual reverse forest process; see `FORMALIZATION_REPORT.md`. -/
theorem theorem_1_3 : FirstPairDeletionClaim := firstPairDeletionClaim

/-- Proposition 1.1(i), including the same-witness consequence for deleting
only the freezing step. The proof uses polynomial continuation sizes. -/
theorem proposition_1_1_i : RemoveFreezeAttachClaim := removeFreezeAttachClaim

/-- Proposition 1.1(ii): removing the specified attachment/freezing pair
can increase the actual expected height by any prescribed positive amount. -/
theorem proposition_1_1_ii : RemoveAttachFreezeClaim := removeAttachFreezeClaim

/-- Proposition 1.1(iii): removing the specified attachment step can strictly
increase expected height. Analytic existence proof, without a numerical witness. -/
theorem proposition_1_1_iii : RemoveAttachClaim := removeAttachClaim

/-- All three assertions of Proposition 1.1, with each original target intact. -/
theorem proposition_1_1 :
    RemoveFreezeAttachClaim ∧ RemoveAttachFreezeClaim ∧ RemoveAttachClaim :=
  ⟨removeFreezeAttachClaim, removeAttachFreezeClaim, removeAttachClaim⟩

/-- The asserted necessity in Question 2: any sequence of clipping thresholds
satisfying the uniform domination property must tend to infinity. -/
theorem question_2_threshold_divergence : Question2ThresholdDivergenceClaim :=
  question2_threshold_divergence

/-- Section 2.5's stronger eventual comparison for the same two words. -/
theorem proposition_1_1_iii_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      (removalLong n).expectedHeight < (removalShort n).expectedHeight :=
  removal_reversal_eventually

/-- The expectation reversal does not give stochastic domination (source III11). -/
theorem removal_not_stochastic_domination {n : ℕ} (hn : 1 ≤ n) :
    ¬Word.HeightLE (removalLong n) (removalShort n) := removal_not_heightLE hn

/-- The height-one probability of the `n`-edge recursive tree is `1/n!`. -/
theorem rrt_height_one_probability {n : ℕ} (hn : 1 ≤ n) :
    (Word.heightLaw (List.replicate n true)).real {1} = (1 : ℝ) / (Nat.factorial n : ℝ) := by
  rw [RRT.replicate_heightLaw]
  exact RRT.height_one_real_mass hn

/-- The height-one probability of the alternating tree with `n` edges is
`2^{-(n-1)}`. -/
theorem alternating_height_one_probability {n : ℕ} (hn : 1 ≤ n) :
    (alternatingWord n).heightLaw.real {1} = (1 : ℝ) / (2 ^ (n - 1) : ℕ) :=
  Alternating.height_one_real_mass hn

/-- Observation 2.1: for every `n ≥ 3` the alternating tree's height does not
stochastically dominate the height of the `n`-edge recursive tree. -/
theorem observation_2_1 {n : ℕ} (hn : 3 ≤ n) :
    ¬ Word.HeightLE (List.replicate n true) (alternatingWord n) :=
  Alternating.not_heightLE_rrt hn

/-- First-edge split of the recursive tree: a uniform root-component edge count
`k` and, given `k`, independent actual `k`-edge and `(n-k)`-edge recursive trees.
Both components are full relabelled forward states. -/
theorem rrt_first_edge_split (n : ℕ) :
    (Forward.treeLaw RRT.allAttach (n + 1)).map (RRTSplit.firstEdgeSplit n) =
      (Measure.uniformOfFinset (Finset.range (n + 1))).bind (fun k =>
        ((Forward.treeLaw RRT.allAttach k).prod
          (Forward.treeLaw RRT.allAttach (n - k))).map (fun p => (k, p.1, p.2))) :=
  RRTSplit.first_edge_split_joint_law n

/-- The lower bound asserted in open question (3) (item Q3a): any sequence of attachment
counts for which every tree with `N n` attachments dominates the `n`-edge recursive tree
satisfies `liminf N n / (n log₂ n) ≥ 1`, in its quantitative `ε` form. The question itself
(the least such `N n`) remains open. -/
theorem question_3_lower_bound : Question3LowerBoundClaim := question3_lowerBound

end FreezingGrowth.Paper
