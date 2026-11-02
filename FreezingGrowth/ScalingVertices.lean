module

public import FreezingGrowth.ScalingHeight
public import FreezingGrowth.TreeCounts

/-!
# Polynomial height scaling by the actual number of vertices

The cited scaling theorem counts operations. The contextual claim at main.tex
207 uses vertices. The signed-walk count and reciprocal-profile sublinearity
give |T_n|/n → 1/2. This module transports the proved height limit to the actual
random state's vertex-cardinality denominator, with the corresponding factor.
-/

@[expose] public section

namespace FreezingGrowth.Scaling

open Filter MeasureTheory
open scoped Topology ENNReal

/-- The deterministic number of vertices created by the finite schedule. -/
def vertexCount (x : ℕ → ℕ → ℤ) (n : ℕ) : ℕ :=
  FreezingGrowth.plusCount (companionSchedule (x n)) n + 1

theorem vertexCount_pos (x : ℕ → ℕ → ℤ) (n : ℕ) : 0 < vertexCount x n := by
  unfold vertexCount
  omega

/-- The deterministic count is the genuine finite state's vertex count. -/
theorem freezingTreeLaw_vertexCount {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x) (n : ℕ) :
    ∀ᵐ s ∂freezingTreeLaw x n, s.vertices.card = vertexCount x n := by
  have h := FreezingGrowth.Forward.treeLaw_counts (companionSchedule (x n)) n
    (companion_before_extinction (x n) (hx n).1 (hx n).2).le
  exact h.mono fun _ hs => hs.2

theorem twice_vertexCount {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x) (n : ℕ) :
    2 * (vertexCount x n : ℤ) = n + 1 + activeCount (x n) n := by
  have h := FreezingGrowth.activeCount_eq (companionSchedule (x n)) n
  rw [companion_activeCount (x n) (hx n).1] at h
  unfold vertexCount
  push_cast
  omega

/-- The operation count is asymptotically twice the actual vertex count. -/
theorem vertexCount_div_time_tendsto_half {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ => (vertexCount x n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  have hS : Tendsto (fun n : ℕ => (activeCount (x n) n : ℝ) / n) atTop (𝓝 0) := by
    simpa using population_sublinear_at hx hα hL1 hpos (by norm_num : (0 : ℝ) < 1) le_rfl
  have hlim : Tendsto (fun n : ℕ =>
      (1 + 1 / (n : ℝ) + (activeCount (x n) n : ℝ) / n) / 2) atTop (𝓝 (1 / 2)) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))).add hS).div_const 2
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : 2 * (vertexCount x n : ℝ) = n + 1 + activeCount (x n) n := by
    exact_mod_cast twice_vertexCount hx n
  field_simp
  nlinarith

theorem time_div_vertexCount_tendsto_two {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ => (n : ℝ) / vertexCount x n) atTop (𝓝 2) := by
  simpa only [inv_div, div_one] using
    (vertexCount_div_time_tendsto_half hx hα hL1 hpos).inv₀ (by norm_num)

/-- The deterministic height scale under the actual-vertex normalization. -/
theorem harmonicUpTotal_div_vertexCount_rpow {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ => harmonicUpTotal x n / (vertexCount x n : ℝ) ^ (1 - α))
      atTop (𝓝 ((2 : ℝ) ^ (1 - α) * ((∫ t, g t ∂profileMeasure) / 2))) := by
  have hratio := (time_div_vertexCount_tendsto_two hx hα1 hL1 hpos).rpow_const
    (Or.inl (by norm_num : (2 : ℝ) ≠ 0)) (p := 1 - α)
  have hp := (tendsto_harmonicUpTotal_div_rpow hx hα0 hα1 hL1 hpos).mul hratio
  rw [mul_comm ((∫ t, g t ∂profileMeasure) / 2)] at hp
  apply hp.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hvp : (0 : ℝ) < vertexCount x n := by exact_mod_cast vertexCount_pos x n
  rw [Real.div_rpow hnp.le hvp.le]
  have hne := (Real.rpow_pos_of_pos hnp (1 - α)).ne'
  exact div_mul_div_cancel₀ hne

/-- Polynomial height scaling measured by the actual finite vertex set.
The extra factor accounts exactly for |T_n|/n → 1/2. -/
theorem height_scaling_limit_vertices {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t => 1 / f t))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun s : FreezingGrowth.Forward.State =>
        (FreezingGrowth.Forward.treeHeight s : ℝ) / (s.vertices.card : ℝ) ^ (1 - α) -
          (2 : ℝ) ^ (1 - α) * (∫ t in Set.Icc (0 : ℝ) 1, 1 / (2 * f t)))
      (ENNReal.ofReal p) (freezingTreeLaw x n)) atTop (𝓝 0) := by
  have hpos := positiveProfile_reciprocal hf
  have hτ (n : ℕ) := companion_before_extinction (x n) (hx n).1 (hx n).2
  have hscale (n : ℕ) : FreezingGrowth.heightScale (companionSchedule (x n)) n =
      harmonicUpTotal x n := companion_heightScale (x n) (hx n).1 n
  have hlog : Tendsto (fun n : ℕ => Real.log n /
      FreezingGrowth.heightScale (companionSchedule (x n)) n) atTop (𝓝 0) := by
    simp_rw [hscale]
    exact tendsto_log_div_harmonicUpTotal hx hα0 hα1 hL1 hpos
  have hheight := maximum_height_tendsto_Lp
    (fun n => companionSchedule (x n)) hτ hlog hp
  simp_rw [hscale] at hheight
  have hresult := tendsto_eLpNorm_change_normalization
    (μ := fun n => freezingTreeLaw x n)
    (Z := fun _ s => (FreezingGrowth.Forward.treeHeight s : ℝ))
    (a := harmonicUpTotal x) (s := fun n => (vertexCount x n : ℝ) ^ (1 - α))
    (by simpa using ENNReal.ofReal_le_ofReal hp)
    (eventually_harmonicUpTotal_ne_zero hx hα0 hα1 hL1 hpos)
    (Eventually.of_forall fun n => (Real.rpow_pos_of_pos
      (by exact_mod_cast vertexCount_pos x n : (0 : ℝ) < vertexCount x n) _).ne')
    (harmonicUpTotal_div_vertexCount_rpow hx hα0 hα1 hL1 hpos) hheight
  rw [reciprocal_half_integral] at hresult
  apply hresult.congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [freezingTreeLaw_vertexCount hx n] with s hs
  rw [hs]

/-- E9 in its literal vertex-size normalization, with only the positive
horizons and reciprocal-profile assumptions of the cited source. -/
theorem height_scaling_limit_vertices_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t => 1 / f t))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun s : FreezingGrowth.Forward.State =>
        (FreezingGrowth.Forward.treeHeight s : ℝ) / (s.vertices.card : ℝ) ^ (1 - α) -
          (2 : ℝ) ^ (1 - α) * (∫ t in Set.Icc (0 : ℝ) 1, 1 / (2 * f t)))
      (ENNReal.ofReal p) (freezingTreeLaw x n)) atTop (𝓝 0) := by
  apply (height_scaling_limit_vertices (admissible_initialRowExtension hx)
    hα0 hα1 hf (hasL1ReciprocalProfile_initialRowExtension hL1) hp).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  simp only [freezingTreeLaw, hn]

end FreezingGrowth.Scaling
