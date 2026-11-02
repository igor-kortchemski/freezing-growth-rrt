module

public import FreezingGrowth.AlternatingHeightBounds
public import FreezingGrowth.RRTStarProbability
public import FreezingGrowth.SublinearIncrement
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Sublinear mean height of the actual recursive tree

The elementary upper MGF bound suffices for arbitrarily late small mean
increments. No sharp maximum-height estimate or convergence of all increments
is asserted here.
-/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def meanHeight (n : ℕ) : ℝ :=
  ∫ s, (Forward.treeHeight s : ℝ) ∂Forward.treeLaw allAttach n

theorem meanHeight_eq_word (n : ℕ) :
    meanHeight n = Word.expectedHeight (List.replicate n true) := by
  rw [Word.expectedHeight, replicate_heightLaw, Forward.heightLaw_integral]
  rfl

theorem meanHeight_nonneg (n : ℕ) : 0 ≤ meanHeight n :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

theorem meanHeight_le (n : ℕ) :
    meanHeight n ≤ Real.log (n + 1) + 1 +
      (Real.exp 1 - 1) * heightScale allAttach n := by
  have hj : Real.exp (meanHeight n) ≤
      ∫ s, Real.exp (Forward.treeHeight s : ℝ) ∂Forward.treeLaw allAttach n :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
      isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
      (Forward.treeLaw_integrable_heightTest allAttach n (fun k => (k : ℝ)))
      (by simpa [Function.comp_def] using
        Forward.treeLaw_integrable_exp_treeHeight allAttach n 1)
  have hu := Forward.treeHeight_mgf_upper allAttach n (before_extinction n)
    (θ := 1) (by norm_num)
  have hu' : (∫ s, Real.exp (Forward.treeHeight s : ℝ)
      ∂Forward.treeLaw allAttach n) ≤
      (n + 1) * Real.exp 1 * Real.exp (heightScale allAttach n * (Real.exp 1 - 1)) := by
    simpa [mgf] using hu
  apply Real.exp_le_exp.mp
  calc
    Real.exp (meanHeight n) ≤ _ := hj.trans hu'
    _ = Real.exp (Real.log (n + 1) + 1 +
        (Real.exp 1 - 1) * heightScale allAttach n) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
      congr 1
      congr 1
      ring

theorem meanHeight_div_tendsto_zero :
    Tendsto (fun n : ℕ => meanHeight n / (n : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hn
  have hshift : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 1 hn)
    simpa [Function.comp_def] using h
  have hscale : Tendsto (fun n : ℕ => heightScale allAttach n / (n : ℝ))
      atTop (𝓝 0) := by
    have h := heightScale_div_log_tendsto_one.mul hlog
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp
  have hupper : Tendsto (fun n : ℕ =>
      (Real.log ((n : ℝ) + 1) + 1 + (Real.exp 1 - 1) * heightScale allAttach n) / n)
      atTop (𝓝 0) := by
    have h := (hshift.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hn)).add
      (hscale.const_mul (Real.exp 1 - 1))
    simpa [add_div, mul_div_assoc] using h
  exact squeeze_zero (fun n => div_nonneg (meanHeight_nonneg n) (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right (meanHeight_le n) (Nat.cast_nonneg n)) hupper

theorem meanHeight_affine_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, meanHeight n ≤ ε / 2 * n + C := by
  have hev : ∀ᶠ n : ℕ in atTop, meanHeight n / (n : ℝ) < ε / 2 :=
    (tendsto_order.mp meanHeight_div_tendsto_zero).2 _ (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let C : ℝ := ∑ i ∈ Finset.range (N + 1), |meanHeight i|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C, fun n => ?_⟩
  by_cases hn : n ≤ N
  · have hsingle : |meanHeight n| ≤ C :=
      Finset.single_le_sum (f := fun i : ℕ => |meanHeight i|) (fun _ _ => abs_nonneg _)
        (show n ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
    have hpos : 0 ≤ ε / 2 * (n : ℝ) := by positivity
    linarith [le_abs_self (meanHeight n)]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h := (div_lt_iff₀ hnpos).mp (hN n (by omega))
    linarith

theorem meanHeight_exists_small_increment {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ meanHeight (n + 1) - meanHeight n < ε :=
  exists_small_increment_of_affine_upper meanHeight hε (meanHeight_affine_upper hε) N

end FreezingGrowth.RRT
