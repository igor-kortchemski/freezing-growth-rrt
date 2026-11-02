module

public import FreezingGrowth.PWIT.HeightBridge
public import FreezingGrowth.RRTSeedIndex
public import FreezingGrowth.RRTLowerDeficit

/-!
# Transferring a positive clock success probability to actual RRT heights

This module proves the transfer with the clock estimate as an explicit
premise. Its actual moment proof is in `PWIT.GlobalSecondMoment`, and the
unconditional height conclusions are assembled in `UniformHeightBounds`.
-/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory Filter
open scoped NNReal Topology

namespace PWIT

/-- The uniform one-sided generation-time estimate, proved by `clockLowerSeed`
in `PWIT.GlobalSecondMoment`, not assumed by the clock construction. -/
def ClockLowerSeed : Prop :=
  ∃ p K : ℝ, ∃ d₀ : ℕ, 0 < p ∧ p ≤ 1 ∧
    ∀ d : ℕ, d₀ ≤ d → p ≤ law.real (reaches d (timeCenter d + K))

end PWIT

namespace RRT

/-- A positive-success clock estimate supplies the seed on the genuine RRT
laws, with the geometric index interpreted as the number of edges. -/
theorem constantSuccessSeed_of_clockLowerSeed (hs : PWIT.ClockLowerSeed) :
    ConstantSuccessSeed 2 := by
  obtain ⟨p, K, d₀, hp, hp1, hs⟩ := hs
  have hp2 : 0 < p / 2 := half_pos hp
  have hp21 : p / 2 ≤ 1 := by linarith
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hev : ∀ᶠ n : ℕ in atTop,
      lowerTail n (lowerCenter 2 n - 1) ≤ 1 - p / 2 := by
    filter_upwards [tendsto_seedIndex.eventually_ge_atTop (max d₀ 1),
      tendsto_seedIndex_time_gap.eventually_le_atBot (Real.log (p / 2) - K),
      hlog.eventually_ge_atTop (-Real.log (p / 2))] with n hd htime hnonneg
    let t : ℝ≥0 := ⟨Real.log ((n : ℝ) + 1) + Real.log (p / 2), by linarith⟩
    have hd0 : d₀ ≤ seedIndex n := (le_max_left d₀ 1).trans hd
    have hdpos : 0 < seedIndex n := by
      have := (le_max_right d₀ 1).trans hd
      omega
    have htime' : PWIT.timeCenter (seedIndex n) + K ≤ (t : ℝ) := by
      change PWIT.timeCenter (seedIndex n) + K ≤
        Real.log ((n : ℝ) + 1) + Real.log (p / 2)
      linarith
    have hclock : p ≤ PWIT.law.real (PWIT.reaches (seedIndex n) (t : ℝ)) :=
      (hs _ hd0).trans (measureReal_mono (PWIT.reaches_mono_time htime'))
    rw [PWIT.reaches_probability_eq_geometric_tail t _ hdpos] at hclock
    have hexp : Real.exp (t : ℝ) = ((n : ℝ) + 1) * (p / 2) := by
      change Real.exp (Real.log ((n : ℝ) + 1) + Real.log (p / 2)) = _
      rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log hp2]
    have hindex : (geometricIndexLaw t).real {k | n < k} ≤ p / 2 := by
      apply (geometricIndexLaw_tail_le_mean t n).trans
      rw [hexp]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      nlinarith
    have htransfer := geometricHeightLaw_tail_le t n (seedIndex n)
    have hheight : p / 2 ≤
        (Forward.heightLaw allAttach n).real {h | seedIndex n ≤ h} := by
      linarith
    have he : {h : ℕ | (h : ℝ) < lowerCenter 2 n - 1} =
        {h : ℕ | seedIndex n ≤ h}ᶜ := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, seedIndex, Nat.ceil_le, not_le]
    rw [lowerTail, he, measureReal_compl (Set.to_countable _).measurableSet, probReal_univ]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact constantSuccessSeed_of_eventual (by norm_num : (0 : ℝ) ≤ 2) hp2 hp21 N hN

end RRT
end FreezingGrowth
