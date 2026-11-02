module

public import FreezingGrowth.FiniteLowProfile
public import FreezingGrowth.MainStatements
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The low-population branch of Theorem 1.2

The printed cutoff in `main.tex`, lines 891–945, is `floor (n / (3 log n))`.
We use the weaker real upper cap `n / (3 log n)` at attachment times. This
allows the finite endpoint-complete estimates to be centered exactly at
`3 log n`, and gives the same error term as the paper. A floor-cutoff bridge
below verifies that every word in the printed low-values branch satisfies
this cap.

These are uniform conclusions for this branch only. The high-population
branch, the full main theorem, and the separate binomial-domination claim
are not asserted here.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory Filter
open scoped Topology

/-- Bennett's rate is strictly positive on the positive half-line. -/
theorem bennettRate_pos {u : ℝ} (hu : 0 < u) : 0 < bennettRate u := by
  have hh := Real.self_sub_one_lt_mul_log (x := 1 + u) (by linarith) (by linarith)
  unfold bennettRate
  linarith

/-- The error appearing at the end of the paper's low-values argument. -/
noncomputable def lowPopulationError (n : ℕ) : ℝ :=
  Real.exp (-(3 * Real.log n) * bennettRate (1 - (Real.exp 1) / 3))

theorem lowPopulation_rate_pos : 0 < bennettRate (1 - (Real.exp 1) / 3) :=
  bennettRate_pos (by have := Real.exp_one_lt_three; linarith)

/-- The displayed error is independent of the choice word and tends to zero. -/
theorem tendsto_lowPopulationError :
    Tendsto lowPopulationError atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ =>
      (3 * Real.log (n : ℝ)) * bennettRate (1 - (Real.exp 1) / 3)) atTop atTop :=
    (hl.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).atTop_mul_const lowPopulation_rate_pos
  change Tendsto (fun n : ℕ =>
    Real.exp (-(3 * Real.log n) * bennettRate (1 - (Real.exp 1) / 3))) atTop (𝓝 0)
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hh)

theorem eventually_log_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1)

namespace Word

/-- A real population cap covering the printed low-values branch. Only the
post-attachment counts enter the active-height mean and its MGF. -/
def LowPopulation (n : ℕ) (xs : Word) : Prop :=
  ∀ i < xs.length, xs.toSigns (i + 1) = true →
    (activeCount xs.toSigns (i + 1) : ℝ) ≤ (n : ℝ) / (3 * Real.log n)

/-- The strict integer cutoff used in the manuscript implies our real cap. -/
theorem lowPopulation_of_floor_cutoff {n : ℕ} {xs : Word}
    (hcap : ∀ i < xs.length,
      activeCount xs.toSigns (i + 1) < ⌊(n : ℝ) / (3 * Real.log n)⌋) :
    LowPopulation n xs := by
  intro i hi _
  have hh : (activeCount xs.toSigns (i + 1) : ℝ) <
      (⌊(n : ℝ) / (3 * Real.log n)⌋ : ℝ) := by exact_mod_cast hcap i hi
  exact hh.le.trans (Int.floor_le _)

private theorem populationCap_pos {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ)) :
    0 < (n : ℝ) / (3 * Real.log n) := by
  have hn : n ≠ 0 := by intro hn; norm_num [hn] at hlog
  exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (by linarith)

private theorem attachment_div_populationCap {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ)) :
    (n : ℝ) / ((n : ℝ) / (3 * Real.log n)) = 3 * Real.log n := by
  have hn : n ≠ 0 := by intro hn; norm_num [hn] at hlog
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

private theorem mainThreshold_le_exp_log {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ)) :
    mainThreshold n ≤ Real.exp 1 * Real.log n := by
  have hh := Real.log_nonneg hlog
  unfold mainThreshold
  linarith

/-- The paper's eventual expectation threshold throughout the low branch,
including words ending with terminal extinction. -/
theorem lowPopulation_expectedHeight {n : ℕ} {xs : Word}
    (hf : InFamily n xs) (hlog : 1 ≤ Real.log (n : ℝ))
    (hcap : LowPopulation n xs) : mainThreshold n ≤ xs.expectedHeight := by
  have hh := profile_expected_lower_bound xs hf.1 (populationCap_pos hlog) hcap
  rw [hf.2, attachment_div_populationCap hlog] at hh
  apply (mainThreshold_le_exp_log hlog).trans
  exact (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by linarith)).trans hh

/-- The explicit lower-tail estimate from the last display in the low-values
argument, obtained directly from the actual finite-word tree law. -/
theorem lowPopulation_failure_bound {n : ℕ} {xs : Word}
    (hf : InFamily n xs) (hlog : 1 ≤ Real.log (n : ℝ))
    (hcap : LowPopulation n xs) :
    xs.heightLaw.real {h : ℕ | (h : ℝ) < mainThreshold n} ≤ lowPopulationError n := by
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hn : n ≠ 0 := by intro hn; norm_num [hn] at hlog
  have hattach : 0 < xs.attachments := by rw [hf.2]; exact Nat.pos_of_ne_zero hn
  have ht : 0 < (3 - Real.exp 1) * Real.log (n : ℝ) :=
    mul_pos (sub_pos.mpr Real.exp_one_lt_three) hlpos
  have hh := profile_height_lower_tail xs hf.1 hattach (populationCap_pos hlog) hcap ht
  rw [hf.2, attachment_div_populationCap hlog] at hh
  have hcenter : 3 * Real.log (n : ℝ) - (3 - Real.exp 1) * Real.log n =
      Real.exp 1 * Real.log n := by ring
  have hratio : ((3 - Real.exp 1) * Real.log (n : ℝ)) / (3 * Real.log n) =
      1 - (Real.exp 1) / 3 := by field_simp
  rw [hcenter, hratio] at hh
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hh
  intro h hh
  exact hh.trans_le (mainThreshold_le_exp_log hlog)

/-- Uniform success probability on the low-population branch for every positive
error tolerance. No assertion about the complementary branch is made. -/
theorem lowPopulation_uniform_probability :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ xs : Word, InFamily n xs → LowPopulation n xs →
        1 - ε ≤ xs.heightLaw.real {h : ℕ | mainThreshold n ≤ (h : ℝ)} := by
  intro ε hε
  have he : ∀ᶠ n in atTop, lowPopulationError n < ε :=
    (tendsto_order.1 tendsto_lowPopulationError).2 ε hε
  have hboth := eventually_log_ge_one.and he
  obtain ⟨N, hN⟩ := eventually_atTop.1 hboth
  refine ⟨N, fun n hn xs hf hc => ?_⟩
  have hb := lowPopulation_failure_bound hf (hN n hn).1 hc
  have hs : {h : ℕ | mainThreshold n ≤ (h : ℝ)} =
      {h : ℕ | (h : ℝ) < mainThreshold n}ᶜ := by ext h; simp
  rw [hs, measureReal_compl ((Set.to_countable _).measurableSet), probReal_univ]
  linarith [(hN n hn).2]

/-- A single index suffices for every expected-height inequality in the low
branch. This is the low-branch restriction of `UniformHeightExpectationClaim`. -/
theorem lowPopulation_uniform_expectation :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ xs : Word, InFamily n xs →
      LowPopulation n xs → mainThreshold n ≤ xs.expectedHeight := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_log_ge_one
  exact ⟨N, fun n hn xs hf hc => lowPopulation_expectedHeight hf (hN n hn) hc⟩

end Word
end FreezingGrowth
