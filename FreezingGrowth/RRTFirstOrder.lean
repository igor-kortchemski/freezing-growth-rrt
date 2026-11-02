module

public import FreezingGrowth.RRTRoughAbsoluteDeviation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# First-order recursive-tree height convergence

The actual height law is controlled in normalized absolute mean. This proves
the first-order probability limit recorded in the source, without asserting
the sharper second-order height expansion.
-/

@[expose] public section

namespace FreezingGrowth.RRT

open MeasureTheory Filter
open scoped Topology

theorem regularized_loglog_le {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ)) :
    Real.log (1 + Real.log ((n : ℝ) + 1)) ≤ Real.log 3 + Real.log (Real.log (n : ℝ)) := by
  have hn0 : n ≠ 0 := by
    intro hn
    simp only [hn, Nat.cast_zero, Real.log_zero] at hlog
    linarith
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hsucc : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (show (n : ℝ) + 1 ≤ 2 * (n : ℝ) by linarith)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnr.ne'] at hh
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have harg : 1 + Real.log ((n : ℝ) + 1) ≤ 3 * Real.log (n : ℝ) := by linarith
  have hpositive : 0 < 1 + Real.log ((n : ℝ) + 1) := by
    have hh : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
  have hh := Real.log_le_log hpositive harg
  rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlogpos.ne'] at hh

theorem tendsto_regularized_loglog_div_log :
    Tendsto (fun n : ℕ => Real.log (1 + Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hupper : Tendsto (fun n : ℕ =>
      (Real.log 3 + Real.log (Real.log (n : ℝ))) / Real.log (n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, div_eq_mul_inv, add_mul, mul_zero, add_zero, Function.comp_apply, id_eq] using
      (hinv.const_mul (Real.log 3)).add hsmall
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hlog.eventually_ge_atTop 1] with n hn
    apply div_nonneg _ (by linarith)
    apply Real.log_nonneg
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 1 by
      have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  · filter_upwards [hlog.eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (regularized_loglog_le hn) (by linarith)

theorem tendsto_rough_error_div_log (C : ℝ) :
    Tendsto (fun n : ℕ => (C + 2 * Real.log (1 + Real.log ((n : ℝ) + 1))) /
      Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc := (tendsto_inv_atTop_zero.comp hlog).const_mul C
  have hh := tendsto_regularized_loglog_div_log.const_mul 2
  simpa only [add_div, div_eq_mul_inv, add_mul, mul_assoc, Function.comp_apply, mul_zero, add_zero] using hc.add hh

theorem integral_abs_sub_log_center_le (n : ℕ) (hn : 1 ≤ n) :
    (∫ h : ℕ, |(h : ℝ) - Real.exp 1 * Real.log (n : ℝ)|
      ∂Forward.heightLaw allAttach n) ≤ roughAbsoluteDeviation n + Real.exp 1 * Real.log 2 := by
  let b := Real.exp 1 * Real.log (n : ℝ)
  let c := Real.exp 1 * Real.log ((n : ℝ) + 1)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbc : b ≤ c := mul_le_mul_of_nonneg_left
    (Real.log_le_log hnpos (by linarith)) (Real.exp_pos _).le
  have hlogs : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + Real.log 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (show (n : ℝ) + 1 ≤ (n : ℝ) * 2 by linarith)
    rwa [Real.log_mul hnpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
  have hshift : c - b ≤ Real.exp 1 * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hlogs (Real.exp_pos 1).le
    dsimp [b, c]
    nlinarith
  have hp (h : ℕ) : |(h : ℝ) - b| ≤ |(h : ℝ) - c| + Real.exp 1 * Real.log 2 := by
    have hu := le_abs_self ((h : ℝ) - c)
    have hl := neg_le_abs ((h : ℝ) - c)
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ ∫ h : ℕ, (|(h : ℝ) - c| + Real.exp 1 * Real.log 2)
        ∂Forward.heightLaw allAttach n :=
      integral_mono (Forward.heightLaw_integrable allAttach n _)
        ((roughAbsoluteDeviation_integrable n).add (integrable_const _)) hp
    _ = _ := by
      rw [integral_add (roughAbsoluteDeviation_integrable n) (integrable_const _), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl

noncomputable def firstOrderAbsoluteDeviation (n : ℕ) : ℝ :=
  ∫ h : ℕ, |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1| ∂Forward.heightLaw allAttach n

theorem firstOrderAbsoluteDeviation_nonneg (n : ℕ) : 0 ≤ firstOrderAbsoluteDeviation n :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem firstOrderAbsoluteDeviation_integrable (n : ℕ) :
    Integrable (fun h : ℕ => |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1|)
      (Forward.heightLaw allAttach n) := Forward.heightLaw_integrable allAttach n _

theorem firstOrderAbsoluteDeviation_le (n : ℕ) (hn : 2 ≤ n) :
    firstOrderAbsoluteDeviation n ≤
      (roughAbsoluteDeviation n + Real.exp 1 * Real.log 2) / Real.log (n : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hp (h : ℕ) : |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1| =
      |(h : ℝ) - Real.exp 1 * Real.log (n : ℝ)| / Real.log (n : ℝ) := by
    calc
      _ = |((h : ℝ) - Real.exp 1 * Real.log (n : ℝ)) / Real.log (n : ℝ)| := by
        congr 1
        field_simp [hlog.ne']
      _ = _ := by rw [abs_div, abs_of_pos hlog]
  calc
    firstOrderAbsoluteDeviation n =
        ∫ h : ℕ, |(h : ℝ) - Real.exp 1 * Real.log (n : ℝ)| / Real.log (n : ℝ)
          ∂Forward.heightLaw allAttach n := integral_congr_ae (Eventually.of_forall hp)
    _ = (∫ h : ℕ, |(h : ℝ) - Real.exp 1 * Real.log (n : ℝ)|
        ∂Forward.heightLaw allAttach n) / Real.log (n : ℝ) := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right (integral_abs_sub_log_center_le n (by omega)) hlog.le

/-- The first-order height estimate holds in normalized absolute mean. -/
theorem tendsto_firstOrderAbsoluteDeviation : Tendsto firstOrderAbsoluteDeviation atTop (𝓝 0) := by
  obtain ⟨C, _, hrough⟩ := uniformRoughAbsoluteDeviation
  apply squeeze_zero' (Eventually.of_forall firstOrderAbsoluteDeviation_nonneg) _
    (tendsto_rough_error_div_log (C + Real.exp 1 * Real.log 2))
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  apply (firstOrderAbsoluteDeviation_le n hn).trans
  apply div_le_div_of_nonneg_right _ hlog
  have hh := hrough n
  linarith

theorem firstOrder_probability_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (Forward.heightLaw allAttach n).real
      {h | ε ≤ |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1|} ≤ firstOrderAbsoluteDeviation n / ε := by
  let E : Set ℕ := {h | ε ≤ |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1|}
  have hp (h : ℕ) : E.indicator (fun _ => ε) h ≤
      |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1| := by
    by_cases hh : h ∈ E
    · rw [Set.indicator_of_mem hh]
      exact hh
    · rw [Set.indicator_of_notMem hh]
      exact abs_nonneg _
  have hmono := integral_mono ((integrable_const ε).indicator (by measurability : MeasurableSet E))
    (firstOrderAbsoluteDeviation_integrable n) hp
  rw [integral_indicator_const _ (by measurability), smul_eq_mul] at hmono
  exact (le_div_iff₀ hε).mpr hmono

/-- The RRT part of the source's first-order in-probability comparison. -/
theorem heightLaw_firstOrder_in_probability {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Forward.heightLaw allAttach n).real
      {h | ε ≤ |(h : ℝ) / Real.log (n : ℝ) - Real.exp 1|}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => firstOrder_probability_le n hε)
  simpa only [zero_div] using tendsto_firstOrderAbsoluteDeviation.div_const ε

theorem abs_meanHeight_div_log_sub_le (n : ℕ) :
    |meanHeight n / Real.log (n : ℝ) - Real.exp 1| ≤ firstOrderAbsoluteDeviation n := by
  have hi := Forward.heightLaw_integrable allAttach n (fun h : ℕ => (h : ℝ))
  have he : (∫ h : ℕ, ((h : ℝ) / Real.log (n : ℝ) - Real.exp 1)
      ∂Forward.heightLaw allAttach n) = meanHeight n / Real.log (n : ℝ) - Real.exp 1 := by
    rw [integral_sub (hi.div_const _) (integrable_const _), integral_div,
      integral_const, Forward.heightLaw_integral]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rfl
  rw [← he]
  exact abs_integral_le_integral_abs

theorem meanHeight_div_log_tendsto_exp_one :
    Tendsto (fun n : ℕ => meanHeight n / Real.log (n : ℝ)) atTop (𝓝 (Real.exp 1)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _) abs_meanHeight_div_log_sub_le
    tendsto_firstOrderAbsoluteDeviation

end FreezingGrowth.RRT
