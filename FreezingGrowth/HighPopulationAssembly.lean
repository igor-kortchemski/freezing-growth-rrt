module

public import FreezingGrowth.RRTLowerDeficit
public import FreezingGrowth.HighPopulationWeakCentering
public import FreezingGrowth.HighPopulationDomination

/-! The exact M2 conclusions from a bounded positive RRT deficit.
The estimate is an explicit premise of these helpers and is supplied by
`UniformHeightBounds` for the unconditional theorem. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory Filter
open scoped Topology

namespace Word

theorem HeightLE.real_tail {xs ys : Word} (h : HeightLE xs ys) (t : ℝ) :
    xs.heightLaw.real {k | t ≤ (k : ℝ)} ≤ ys.heightLaw.real {k | t ≤ (k : ℝ)} := by
  have he : {k : ℕ | Nat.ceil t ≤ k} = {k : ℕ | t ≤ (k : ℝ)} := by
    ext k
    simp only [Set.mem_ofPred_eq, Nat.ceil_le]
  have hh := h (Nat.ceil t)
  rw [he] at hh
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

/-- Match integer cutoff subtraction with the natural attachment count. -/
theorem high_population_at_cutoff {n : ℕ} {xs : Word}
    (hr : 0 < populationCutoff n) (ha : xs.admissible)
    (hh : ∃ j, 1 ≤ j ∧ j ≤ xs.length ∧ populationCutoff n ≤ activeCount xs.toSigns j) :
    HeightLE (List.replicate (highPopulationIndex n) true) xs := by
  let r : ℕ := (populationCutoff n).toNat
  have hr' : (r : ℤ) = populationCutoff n := Int.toNat_of_nonneg (by omega)
  have hi : r - 1 = highPopulationIndex n := by unfold highPopulationIndex; omega
  rw [← hi]
  apply high_population_domination xs ha
  obtain ⟨j, hj, hj', hhigh⟩ := hh
  exact ⟨j, hj', by simpa only [hr'] using hhigh⟩

end Word

/-- Uniform high-branch expectation, with the estimate premise visible. -/
theorem highPopulation_uniform_expectation_of_deficit {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c < 5 - Real.exp 1) (hd : RRT.UniformLowerDeficit c) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ xs : Word, Word.InFamily n xs →
      (∃ j, 1 ≤ j ∧ j ≤ xs.length ∧ populationCutoff n ≤ activeCount xs.toSigns j) →
      mainThreshold n ≤ xs.expectedHeight := by
  obtain ⟨C, hC, hbound⟩ := hd
  have hg := (tendsto_highPopulation_lowerCenter_gap hc hsmall).eventually_ge_atTop C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hg.and eventually_populationCutoff_pos)
  refine ⟨N, fun n hn xs hf hh => ?_⟩
  have hm := RRT.lowerCenter_sub_deficit_le_mean c (highPopulationIndex n)
  have hb := hbound (highPopulationIndex n)
  have hcomp := (Word.high_population_at_cutoff (hN n hn).2 hf.1 hh).expectedHeight_le
  rw [← RRT.meanHeight_eq_word] at hcomp
  have hgap := (hN n hn).1
  linarith

/-- Uniform high-branch probability, derived directly from the positive deficit. -/
theorem highPopulation_uniform_probability_of_deficit {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c < 5 - Real.exp 1) (hd : RRT.UniformLowerDeficit c) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ xs : Word, Word.InFamily n xs →
      (∃ j, 1 ≤ j ∧ j ≤ xs.length ∧ populationCutoff n ≤ activeCount xs.toSigns j) →
      1 - ε ≤ xs.heightLaw.real {h | mainThreshold n ≤ (h : ℝ)} := by
  obtain ⟨C, hC, hbound⟩ := hd
  intro ε hε
  have hg := (tendsto_highPopulation_lowerCenter_gap hc hsmall).eventually_ge_atTop
    (C / ε + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hg.and eventually_populationCutoff_pos)
  refine ⟨N, fun n hn xs hf hh => ?_⟩
  let m := highPopulationIndex n
  have hgap := (hN n hn).1
  have hpos : mainThreshold n < RRT.lowerCenter c m := by
    have := div_nonneg hC hε.le
    dsimp [m]
    linarith
  have hm := RRT.gap_mul_lowerTail_le_deficit c (mainThreshold n) m
  have hb := hbound m
  have hfail : RRT.lowerTail m (mainThreshold n) ≤ ε := by
    have hmult := (div_le_iff₀ hε).mp (show C / ε ≤
      RRT.lowerCenter c m - mainThreshold n by dsimp [m]; linarith)
    nlinarith
  have hsuccess : 1 - ε ≤ (Forward.heightLaw RRT.allAttach m).real
      {h | mainThreshold n ≤ (h : ℝ)} := by
    have he : {h : ℕ | mainThreshold n ≤ (h : ℝ)} =
        {h : ℕ | (h : ℝ) < mainThreshold n}ᶜ := by ext h; simp
    rw [he, measureReal_compl (by measurability), probReal_univ]
    exact sub_le_sub_left hfail 1
  have hcomp := (Word.high_population_at_cutoff (hN n hn).2 hf.1 hh).real_tail (mainThreshold n)
  rw [RRT.replicate_heightLaw] at hcomp
  exact hsuccess.trans hcomp

/-- Exact paper targets, still conditional on the remaining RRT estimate. -/
theorem uniformHeightClaims_of_deficit {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c < 5 - Real.exp 1) (hd : RRT.UniformLowerDeficit c) :
    UniformHeightProbabilityClaim ∧ UniformHeightExpectationClaim := by
  constructor
  · intro ε hε
    obtain ⟨N1, h1⟩ := highPopulation_uniform_probability_of_deficit hc hsmall hd ε hε
    obtain ⟨N2, h2⟩ := Word.lowPopulation_uniform_probability ε hε
    refine ⟨max N1 N2, fun n hn xs hf => ?_⟩
    rcases Word.population_dichotomy n xs with hh | hl
    · exact h1 n (le_trans (le_max_left _ _) hn) xs hf hh
    · exact h2 n (le_trans (le_max_right _ _) hn) xs hf (Word.lowPopulation_of_small_profile hl)
  · obtain ⟨N1, h1⟩ := highPopulation_uniform_expectation_of_deficit hc hsmall hd
    obtain ⟨N2, h2⟩ := Word.lowPopulation_uniform_expectation
    refine ⟨max N1 N2, fun n hn xs hf => ?_⟩
    rcases Word.population_dichotomy n xs with hh | hl
    · exact h1 n (le_trans (le_max_left _ _) hn) xs hf hh
    · exact h2 n (le_trans (le_max_right _ _) hn) xs hf (Word.lowPopulation_of_small_profile hl)

/-- The single constant-success estimate at coefficient two suffices for M2. -/
theorem uniformHeightClaims_of_seed (hs : RRT.ConstantSuccessSeed 2) :
    UniformHeightProbabilityClaim ∧ UniformHeightExpectationClaim :=
  uniformHeightClaims_of_deficit (by norm_num)
    (by have := Real.exp_one_lt_three; linarith)
    (RRT.uniformLowerDeficit_of_seed (by norm_num) hs)

end FreezingGrowth
