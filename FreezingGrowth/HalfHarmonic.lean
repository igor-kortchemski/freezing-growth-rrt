module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

/-! The harmonic window governing the larger first-edge component. -/

@[expose] public section
namespace FreezingGrowth

open Filter
open scoped Topology

theorem tendsto_nat_half_ratio :
    Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => ((n % 2 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (fun n => div_le_div_of_nonneg_right (show ((n % 2 : ℕ) : ℝ) ≤ 1 by
        exact_mod_cast (show n % 2 ≤ 1 by omega)) (Nat.cast_nonneg n))
    exact tendsto_const_nhds.div_atTop hn
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub (hm.div_const 2)
  simp only [zero_div, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have he : (n : ℝ) = ((n % 2 : ℕ) : ℝ) + 2 * ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n 2).symm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  linarith

theorem tendsto_nat_half : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2 * b)] with n hn
  omega

theorem tendsto_half_harmonic :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) - (harmonic (n / 2) : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / ((n / 2 : ℕ) : ℝ)) atTop (𝓝 2) := by
    simpa [inv_div] using
      tendsto_nat_half_ratio.inv₀ (by norm_num)
  have hlog := hr.log (by norm_num : (2 : ℝ) ≠ 0)
  have hd := Real.tendsto_harmonic_sub_log.sub
    (Real.tendsto_harmonic_sub_log.comp tendsto_nat_half)
  have h := hd.add hlog
  simp only [sub_self, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hh0 : (((n / 2 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show n / 2 ≠ 0 by omega)
  rw [Real.log_div hn0 hh0]
  dsimp only [Function.comp_def]
  ring

theorem eventually_half_harmonic_contraction :
    ∀ᶠ n : ℕ in atTop,
      (10 / 7 : ℝ) * ((n : ℝ) + 1) / n *
        ((harmonic n : ℝ) - (harmonic (n / 2) : ℝ)) ≤ 1 := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hn)
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have h := (hr.const_mul (10 / 7 : ℝ)).mul tendsto_half_harmonic
  have hlt : (10 / 7 : ℝ) * 1 * Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have he := (tendsto_order.mp h).2 1 hlt
  filter_upwards [he] with n hn
  simpa only [mul_div_assoc] using hn.le

end FreezingGrowth
