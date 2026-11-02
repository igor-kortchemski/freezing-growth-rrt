module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Elementary analytic limits for the old-tree residual envelope. Source-specific
rates and the comparison with the actual residual are established separately. -/

@[expose] public section
namespace FreezingGrowth.RRTSplit

open Filter
open scoped Topology

theorem tendsto_affine_exp_decay (α κ B L : ℝ) (hα : 0 < α) (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => (x + L) * Real.exp (α * (B - κ * x))) atTop (𝓝 0) := by
  have hc : 0 < α * κ := mul_pos hα hκ
  have hlinear : Tendsto (fun x : ℝ => x * Real.exp (-(α * κ) * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (α * κ) hc
  have hconstant : Tendsto (fun x : ℝ => Real.exp (-(α * κ) * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (α * κ) hc
  have hh : Tendsto
      (fun x : ℝ => Real.exp (α * B) *
        (x * Real.exp (-(α * κ) * x) + L * Real.exp (-(α * κ) * x))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hlinear.add (hconstant.const_mul L)).const_mul (Real.exp (α * B))
  convert hh using 1
  funext x
  rw [show α * (B - κ * x) = α * B + -(α * κ) * x by ring, Real.exp_add]
  ring

theorem tendsto_log_exp_decay (α κ B : ℝ) (hα : 0 < α) (hκ : 0 < κ) :
    Tendsto (fun m : ℕ => (Real.log (m : ℝ) + Real.log 2) *
      Real.exp (α * (B - κ * Real.log (m : ℝ)))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def] using
    (tendsto_affine_exp_decay α κ B (Real.log 2) hα hκ).comp hlog

theorem tendsto_upper_residual_exp_decay :
    Tendsto (fun m : ℕ => Real.exp ((1 - Real.exp 1) * Real.log ((m : ℝ) + 1)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ => Real.log ((m : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hc : 1 - Real.exp 1 < 0 := by
    have hh : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  simpa only [Function.comp_def] using
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg hc)

end FreezingGrowth.RRTSplit
