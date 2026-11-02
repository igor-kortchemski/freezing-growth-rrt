module

public import FreezingGrowth.RRTCriticalDeviation
public import FreezingGrowth.RRTLowerTailPaperRate

/-! The source's sharp center and mean-centered concentration, conditional
only on the critical upper clock estimate. No sharp source obligation is
closed by this adapter until that actual clock estimate is supplied. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory Set

noncomputable def sourceHeightCenter (n : ℕ) : ℝ :=
  Real.exp 1 * Real.log (n : ℝ) - (3 / 2) * Real.log (Real.log (n : ℝ))

noncomputable def criticalCenterComparisonConstant : ℝ :=
  Real.exp 1 * Real.log 2 + (3 / 2) * Real.log 5

theorem criticalCenterComparisonConstant_nonneg : 0 ≤ criticalCenterComparisonConstant := by
  unfold criticalCenterComparisonConstant
  positivity

theorem critical_source_center_difference {n : ℕ} (hn : 2 ≤ n) :
    |lowerCenter (3 / 2) n - sourceHeightCenter n| ≤ criticalCenterComparisonConstant := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
    have := Real.log_two_gt_d9
    linarith
  have hl : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hnp (by linarith)
  have hu : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (show (n : ℝ) + 1 ≤ 2 * n by linarith)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnp.ne'] at hh
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hll : Real.log (Real.log (n : ℝ)) ≤ Real.log (1 + Real.log ((n : ℝ) + 1)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hllU : Real.log (1 + Real.log ((n : ℝ) + 1)) ≤
      Real.log 5 + Real.log (Real.log (n : ℝ)) := by
    have hh := Real.log_le_log (by linarith : 0 < 1 + Real.log ((n : ℝ) + 1))
      (show 1 + Real.log ((n : ℝ) + 1) ≤ 5 * Real.log (n : ℝ) by linarith)
    rwa [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by linarith : Real.log (n : ℝ) ≠ 0)] at hh
  have he := Real.exp_pos 1
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h5 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
  have hel := mul_le_mul_of_nonneg_left hl he.le
  have heu := mul_le_mul_of_nonneg_left hu he.le
  have he2 := mul_nonneg he.le h2
  unfold lowerCenter sourceHeightCenter criticalCenterComparisonConstant
  apply abs_le.mpr
  constructor <;> nlinarith

noncomputable def sourceHeightAbsoluteDeviation (n : ℕ) : ℝ :=
  ∫ h : ℕ, |(h : ℝ) - sourceHeightCenter n| ∂Forward.heightLaw allAttach n

theorem sourceHeightAbsoluteDeviation_integrable (n : ℕ) :
    Integrable (fun h : ℕ => |(h : ℝ) - sourceHeightCenter n|) (Forward.heightLaw allAttach n) :=
  Forward.heightLaw_integrable allAttach n _

theorem sourceHeightAbsoluteDeviation_le {n : ℕ} (hn : 2 ≤ n) :
    sourceHeightAbsoluteDeviation n ≤ criticalAbsoluteDeviation n + criticalCenterComparisonConstant := by
  have hp (h : ℕ) : |(h : ℝ) - sourceHeightCenter n| ≤
      |(h : ℝ) - lowerCenter (3 / 2) n| + criticalCenterComparisonConstant := by
    have hh := abs_add_le ((h : ℝ) - lowerCenter (3 / 2) n)
      (lowerCenter (3 / 2) n - sourceHeightCenter n)
    have hc := critical_source_center_difference hn
    rw [sub_add_sub_cancel] at hh
    linarith
  calc
    _ ≤ ∫ h : ℕ, |(h : ℝ) - lowerCenter (3 / 2) n| + criticalCenterComparisonConstant
        ∂Forward.heightLaw allAttach n :=
      integral_mono (sourceHeightAbsoluteDeviation_integrable n)
        ((criticalAbsoluteDeviation_integrable n).add (integrable_const _)) hp
    _ = _ := by
      rw [integral_add (criticalAbsoluteDeviation_integrable n) (integrable_const _), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl

theorem uniformSourceHeightAbsoluteDeviation_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 2 ≤ n → sourceHeightAbsoluteDeviation n ≤ B := by
  obtain ⟨B, hB, hh⟩ := uniformCriticalAbsoluteDeviation_of_clock hclock
  exact ⟨B + criticalCenterComparisonConstant, add_nonneg hB criticalCenterComparisonConstant_nonneg,
    fun n hn => (sourceHeightAbsoluteDeviation_le hn).trans (add_le_add (hh n) le_rfl)⟩

/-- The exact source mean expansion, in a uniform bounded-error form. -/
theorem sourceMeanHeightExpansion_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 2 ≤ n → |meanHeight n - sourceHeightCenter n| ≤ B := by
  obtain ⟨B, hB, hh⟩ := uniformCriticalMeanDeviation_of_clock hclock
  refine ⟨B + criticalCenterComparisonConstant, add_nonneg hB criticalCenterComparisonConstant_nonneg,
    fun n hn => ?_⟩
  have htri := abs_add_le (meanHeight n - lowerCenter (3 / 2) n)
    (lowerCenter (3 / 2) n - sourceHeightCenter n)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans (add_le_add (hh n) (critical_source_center_difference hn))

theorem sourceHeight_probability_le (n : ℕ) {k : ℝ} (hk : 0 < k) :
    (Forward.heightLaw allAttach n).real {h | k ≤ |(h : ℝ) - sourceHeightCenter n|} ≤
      sourceHeightAbsoluteDeviation n / k := by
  let E : Set ℕ := {h | k ≤ |(h : ℝ) - sourceHeightCenter n|}
  have hp (h : ℕ) : E.indicator (fun _ => k) h ≤ |(h : ℝ) - sourceHeightCenter n| := by
    by_cases hh : h ∈ E
    · rw [Set.indicator_of_mem hh]; exact hh
    · rw [Set.indicator_of_notMem hh]; exact abs_nonneg _
  have hm := integral_mono ((integrable_const k).indicator (by measurability : MeasurableSet E))
    (sourceHeightAbsoluteDeviation_integrable n) hp
  rw [integral_indicator_const _ (by measurability), smul_eq_mul] at hm
  exact (le_div_iff₀ hk).mpr hm

/-- Uniform tightness of the source-centered heights, stronger than the
asymptotic `O_P(1)` statement. The finite domain starts at two. -/
theorem sourceHeight_tight_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      (Forward.heightLaw allAttach n).real {h | K ≤ |(h : ℝ) - sourceHeightCenter n|} ≤ ε := by
  obtain ⟨B, hB, hbound⟩ := uniformSourceHeightAbsoluteDeviation_of_clock hclock
  intro ε hε
  let K := B / ε + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun n hn => ?_⟩
  apply (sourceHeight_probability_le n hK).trans
  apply (div_le_iff₀ hK).mpr
  have hh := hbound n hn
  have he : ε * K = B + ε := by dsimp [K]; field_simp
  linarith

/-- The exact numerical rate in the source, centered at the actual mean.
The estimate holds at every size and every nonnegative real threshold. -/
theorem meanCenteredHeightConcentration_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ k : ℝ, 0 ≤ k →
      (Forward.heightLaw allAttach n).real {h | k ≤ |(h : ℝ) - meanHeight n|} ≤
        K * Real.exp (-k / (3 * Real.exp 1)) := by
  obtain ⟨B, hB, hmean⟩ := uniformCriticalMeanDeviation_of_clock hclock
  obtain ⟨A, hA, hupper⟩ := heightLaw_critical_upper_tail_of_clock hclock
  obtain ⟨L, hL, hlower⟩ := lowerTail_paperRate_of_seed
    (by norm_num : (0 : ℝ) ≤ 3 / 2) constantSuccessSeed_critical
  have hC : 0 ≤ C := by
    have hh := hclock d₀ le_rfl 0 le_rfl
    simp only [add_zero, one_pow, neg_zero, Real.exp_zero, mul_one] at hh
    exact measureReal_nonneg.trans hh
  let D := 2 * C * polynomialExpAbsorptionConstant P
  let T := A + B + 1
  let R := 3 * Real.exp 1
  have hD : 0 ≤ D := by dsimp [D]; have := polynomialExpAbsorptionConstant_pos P; positivity
  have hT : 0 ≤ T := by dsimp [T]; linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hR2 : 2 ≤ R := by dsimp [R]; have := Real.exp_one_gt_two; linarith
  refine ⟨(1 + D + L) * Real.exp (T / R), by positivity, fun n k hk => ?_⟩
  have hfactor : Real.exp (-(k - T) / R) = Real.exp (T / R) * Real.exp (-k / R) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (Forward.heightLaw allAttach n).real {h | k ≤ |(h : ℝ) - meanHeight n|} ≤
    ((1 + D + L) * Real.exp (T / R)) * Real.exp (-k / R)
  by_cases hlarge : T ≤ k
  · let x := k - T
    have hx : 0 ≤ x := sub_nonneg.mpr hlarge
    let U : Set ℕ := {h | lowerCenter (3 / 2) n + A + x ≤ (h : ℝ)}
    let V : Set ℕ := {h | (h : ℝ) < lowerCenter (3 / 2) n - x}
    have hsub : {h : ℕ | k ≤ |(h : ℝ) - meanHeight n|} ⊆ U ∪ V := by
      intro h hh
      have hm := abs_le.mp (hmean n)
      change k ≤ |(h : ℝ) - meanHeight n| at hh
      rcases (le_abs.mp hh) with hplus | hminus
      · left
        dsimp [U, x, T]
        linarith
      · right
        dsimp [V, x, T]
        linarith
    have hu : (Forward.heightLaw allAttach n).real U ≤ D * Real.exp (-x / R) := by
      have hh := hupper n x hx
      have hp := mul_le_mul_of_nonneg_left (polynomial_exp_absorption P hx)
        (show 0 ≤ 2 * C by linarith)
      have hfirst : (Forward.heightLaw allAttach n).real U ≤ D * Real.exp (-x / 2) := by
        apply hh.trans
        simpa only [D, mul_assoc] using hp
      apply hfirst.trans
      apply mul_le_mul_of_nonneg_left _ hD
      apply Real.exp_le_exp.mpr
      have hr := div_le_div_of_nonneg_left hx (by norm_num : (0 : ℝ) < 2) hR2
      simpa only [neg_div] using neg_le_neg hr
    have hv : (Forward.heightLaw allAttach n).real V ≤ L * Real.exp (-x / R) := hlower n x hx
    calc
      _ ≤ (Forward.heightLaw allAttach n).real (U ∪ V) := measureReal_mono hsub
      _ ≤ (Forward.heightLaw allAttach n).real U + (Forward.heightLaw allAttach n).real V :=
        measureReal_union_le _ _
      _ ≤ D * Real.exp (-x / R) + L * Real.exp (-x / R) := add_le_add hu hv
      _ ≤ (1 + D + L) * Real.exp (-x / R) := by have := Real.exp_pos (-x / R); nlinarith
      _ = _ := by dsimp [x]; rw [hfactor]; ring
  · have hexp : 1 ≤ Real.exp (-(k - T) / R) := Real.one_le_exp_iff.mpr (by
      apply div_nonneg _ hR.le
      linarith)
    have hcoef : 1 ≤ 1 + D + L := by linarith
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ (1 + D + L) * Real.exp (-(k - T) / R) := one_le_mul_of_one_le_of_one_le hcoef hexp
      _ = _ := by rw [hfactor]; ring

end FreezingGrowth.RRT
