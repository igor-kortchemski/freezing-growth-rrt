module

public import FreezingGrowth.ScalingMomentLimits
public import FreezingGrowth.LowPopulationAsymptotic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual maximum-height convergence above logarithmic scale

Selected Apache-2.0 companion fragments; see SCALING_PROVENANCE.md.
No duplicate tree state or assumed concentration theorem is introduced.
-/

@[expose] public section

namespace FreezingGrowth.Forward

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Convenient fixed-parameter MGF estimate when the height scale dominates `log (n+1)`. -/
theorem treeHeight_mgf_one_le (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x)
    (hN : (n + 1 : ℝ) ≤ Real.exp (heightScale x n))
    (hm : 1 ≤ heightScale x n) :
    mgf (fun s => (treeHeight s : ℝ)) (treeLaw x n) 1 ≤
      Real.exp ((Real.exp 1 + 1) * heightScale x n) := by
  calc
    _ ≤ (n + 1) * Real.exp 1 * Real.exp (heightScale x n * (Real.exp 1 - 1)) :=
      treeHeight_mgf_upper x n hτ (by norm_num)
    _ ≤ Real.exp (heightScale x n) * Real.exp (heightScale x n) *
        Real.exp (heightScale x n * (Real.exp 1 - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hN (Real.exp_le_exp.mpr hm) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp ((Real.exp 1 + 1) * heightScale x n) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end FreezingGrowth.Forward

namespace FreezingGrowth.Scaling

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The function defining the height factor, strictly increasing on `[1, ∞)`. -/
noncomputable def heightRate (x : ℝ) : ℝ := x * Real.log x - x

theorem heightRate_eq (x : ℝ) : heightRate x = x * (Real.log x - 1) := by
  unfold heightRate
  ring

theorem continuous_heightRate : Continuous heightRate :=
  Real.continuous_mul_log.sub continuous_id

theorem hasDerivAt_heightRate {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt heightRate (Real.log x) x := by
  convert (Real.hasDerivAt_mul_log hx).fun_sub (hasDerivAt_id' x) using 1
  · rfl
  · ring

theorem strictMonoOn_heightRate : StrictMonoOn heightRate (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_heightRate.continuousOn ?_
  intro x hx
  have hx1 : 1 < x := by simpa using hx
  rw [(hasDerivAt_heightRate (by linarith)).deriv]
  exact Real.log_pos hx1

@[simp] theorem heightRate_one : heightRate 1 = -1 := by simp [heightRate]

@[simp] theorem heightRate_exp_one : heightRate (Real.exp 1) = 0 := by
  simp [heightRate]

theorem bennettRate_eq_heightRate (u : ℝ) :
    bennettRate u = heightRate (1 + u) + 1 := by
  unfold bennettRate heightRate
  ring

@[simp] theorem bennettRate_zero : bennettRate 0 = 0 := by simp [bennettRate]

theorem strictMonoOn_bennettRate : StrictMonoOn bennettRate (Ici 0) := by
  intro x hx y hy hxy
  rw [bennettRate_eq_heightRate, bennettRate_eq_heightRate]
  have h := strictMonoOn_heightRate
    (show 1 + x ∈ Ici (1 : ℝ) by simp only [mem_Ici] at *; linarith)
    (show 1 + y ∈ Ici (1 : ℝ) by simp only [mem_Ici] at *; linarith)
    (show 1 + x < 1 + y by linarith)
  linarith

theorem log_nat_succ_le_two_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  calc
    Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) * n) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = 2 * Real.log (n : ℝ) := by rw [Real.log_mul hp.ne' hp.ne']; ring

theorem eventually_log_nat_succ_le_mul_scale {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 1) ≤ a * h n := by
  filter_upwards [eventually_ge_atTop 2, hdiv.eventually_gt_atTop 0,
    hlog.eventually (gt_mem_nhds (half_pos ha))] with n hn hhn hsmall
  have hs := (div_lt_iff₀ hhn).mp hsmall
  have hb := log_nat_succ_le_two_log hn
  nlinarith

theorem eventually_nat_succ_le_exp_scale {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ Real.exp (h n) := by
  filter_upwards [eventually_log_nat_succ_le_mul_scale hdiv hlog zero_lt_one] with n hn
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  simpa only [Real.exp_log hpos, one_mul] using Real.exp_le_exp.mpr hn

/-- Any positive exponential rate beats the finite union factor when
`log n = o(h_n)`. -/
theorem tendsto_nat_succ_mul_exp_neg_of_log_negligible {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-h n * a)) atTop (𝓝 0) := by
  have he : Tendsto (fun n => Real.exp (-h n * (a / 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := tendsto_neg_atTop_atBot.comp (hdiv.atTop_mul_const (half_pos ha))
    change Tendsto (fun n : ℕ => -(h n * (a / 2))) atTop atBot at hh
    simpa only [neg_mul] using hh
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ he
  filter_upwards [eventually_log_nat_succ_le_mul_scale hdiv hlog (half_pos ha)] with n hn
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  calc
    ((n : ℝ) + 1) * Real.exp (-h n * a) =
        Real.exp (Real.log ((n : ℝ) + 1) - h n * a) := by
      rw [neg_mul, Real.exp_neg, Real.exp_sub, Real.exp_log hpos, div_eq_mul_inv]
    _ ≤ Real.exp (-h n * (a / 2)) := Real.exp_le_exp.mpr (by nlinarith)

theorem tendsto_shifted_bennett_upper_of_log_negligible {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      Real.exp (-h n * bennettRate (ε - 1 / h n))) atTop (𝓝 0) := by
  have hb := tendsto_nat_succ_mul_exp_neg_of_log_negligible hdiv hlog
    (bennettRate_pos (half_pos hε))
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hb
  filter_upwards [hdiv.eventually_gt_atTop 0, hdiv.eventually_ge_atTop (2 / ε)] with n hn hne
  have hs : 1 / h n ≤ ε / 2 := by
    apply (div_le_iff₀ hn).mpr
    have hm := (div_le_iff₀ hε).mp hne
    nlinarith
  have hle : ε / 2 ≤ ε - 1 / h n := by linarith
  have hg := strictMonoOn_bennettRate.monotoneOn (by positivity : 0 ≤ ε / 2)
    (by linarith : 0 ≤ ε - 1 / h n) hle
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem normalized_treeHeight_lower_tail (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {ε : ℝ} (hε : 0 < ε) :
    (Forward.treeLaw x n).real {s | (Forward.treeHeight s : ℝ) / heightScale x n < 1 - ε} ≤
      Real.exp (-heightScale x n * bennettRate ε) := by
  have hm := heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  have hbound := Forward.treeHeight_lower_tail x n hn hτ (mul_pos hε hm)
  have hq : ε * heightScale x n / heightScale x n = ε := by field_simp
  rw [hq] at hbound
  convert hbound using 1
  congr 1
  ext s
  change (Forward.treeHeight s : ℝ) / heightScale x n < 1 - ε ↔
    (Forward.treeHeight s : ℝ) < heightScale x n - ε * heightScale x n
  rw [div_lt_iff₀ hm]
  ring_nf

theorem normalized_treeHeight_upper_tail (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {ε : ℝ} (ht : 0 < ε * heightScale x n - 1) :
    (Forward.treeLaw x n).real {s | 1 + ε < (Forward.treeHeight s : ℝ) / heightScale x n} ≤
      (n + 1) * Real.exp (-heightScale x n * bennettRate (ε - 1 / heightScale x n)) := by
  have hm := heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  have hbound := Forward.treeHeight_upper_tail x n hn hτ ht
  have hq : (ε * heightScale x n - 1) / heightScale x n = ε - 1 / heightScale x n := by field_simp
  rw [hq] at hbound
  convert hbound using 1
  congr 1
  ext s
  change 1 + ε < (Forward.treeHeight s : ℝ) / heightScale x n ↔
    heightScale x n + 1 + (ε * heightScale x n - 1) < (Forward.treeHeight s : ℝ)
  rw [lt_div_iff₀ hm]
  ring_nf

theorem maximum_height_lower_probability_tendsto_zero (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | (Forward.treeHeight s : ℝ) / heightScale (x n) n < 1 - ε}) atTop (𝓝 0) := by
  have hd := tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  have he : Tendsto (fun n => Real.exp (-heightScale (x n) n * bennettRate ε)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := tendsto_neg_atTop_atBot.comp (hd.atTop_mul_const (bennettRate_pos hε))
    change Tendsto (fun n : ℕ => -(heightScale (x n) n * bennettRate ε)) atTop atBot at hh
    simpa only [neg_mul] using hh
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ he
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact normalized_treeHeight_lower_tail (x n) n hn (hτ n) hε

theorem maximum_height_upper_probability_tendsto_zero (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (x n) n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | 1 + ε < (Forward.treeHeight s : ℝ) / heightScale (x n) n}) atTop (𝓝 0) := by
  have hd := tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (tendsto_shifted_bennett_upper_of_log_negligible hd hlog hε)
  filter_upwards [eventually_ge_atTop 1, hd.eventually_gt_atTop (1 / ε)] with n hn hlarge
  have ht : 0 < ε * heightScale (x n) n - 1 := by
    have hh := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  exact normalized_treeHeight_upper_tail (x n) n hn (hτ n) ht

/-- Convergence in probability of the normalized maximum under `log n = o(h_n⁺)`. -/
theorem maximum_height_deviation_tendsto_zero (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (x n) n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Forward.treeLaw (x n) n)
      {s | ε ≤ |(Forward.treeHeight s : ℝ) / heightScale (x n) n - 1|}) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
  have hl := (maximum_height_lower_probability_tendsto_zero x hτ (half_pos hε)).add
    (maximum_height_upper_probability_tendsto_zero x hτ hlog (half_pos hε))
  simp only [add_zero] at hl
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hl
  intro n
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
  intro s hs
  change ε ≤ |(Forward.treeHeight s : ℝ) / heightScale (x n) n - 1| at hs
  change (Forward.treeHeight s : ℝ) / heightScale (x n) n < 1 - ε / 2 ∨
    1 + ε / 2 < (Forward.treeHeight s : ℝ) / heightScale (x n) n
  rcases le_abs.mp hs with h | h
  · right; linarith
  · left; linarith

/-- The companion maximum-height limit for every real exponent `p ≥ 1`.
Its logarithmic-negligibility premise is proved from the E9 profile assumptions. -/
theorem maximum_height_tendsto_Lp (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (x n) n) atTop (𝓝 0))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun s => (Forward.treeHeight s : ℝ) / heightScale (x n) n - 1)
      (ENNReal.ofReal p) (Forward.treeLaw (x n) n)) atTop (𝓝 0) := by
  have hd := tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  apply normalized_tendsto_Lp_of_eventual_exp_bound
    (Z := fun _ s => (Forward.treeHeight s : ℝ)) (a := fun n => heightScale (x n) n)
    (B := Real.exp 1 + 1)
  · intro n; exact measurable_from_top
  · intro n θ; exact Forward.treeLaw_integrable_exp_treeHeight (x n) n θ
  · intro n; exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · filter_upwards [eventually_nat_succ_le_exp_scale hd hlog, hd.eventually_ge_atTop 1]
      with n hn hm
    exact Forward.treeHeight_mgf_one_le (x n) n (hτ n) hn hm
  · exact hd
  · intro ε hε; exact maximum_height_deviation_tendsto_zero x hτ hlog hε
  · exact hp

end FreezingGrowth.Scaling
