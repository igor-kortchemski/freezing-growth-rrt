module

public import FreezingGrowth.RRTSplitResidualPolynomial
public import FreezingGrowth.RRTLowerTailExponential
public import FreezingGrowth.RRTResidualDecayAsymptotics

/-!
# Decay of the actual old-tree residual uniformly over long suffixes

The comparison uses the actual finite-height support and the larger actual
first-edge component. The exponential lower-tail rate is the one obtained
from the proved clock seed; no specified sharp rate is assumed.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory Filter
open scoped Classical Topology

namespace RRT

theorem upperExcessAt_le_support_tail (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    upperExcessAt m T ≤ (m : ℝ) *
      (Forward.heightLaw allAttach m).real {h | T < (h : ℝ)} := by
  let E : Set ℕ := {h | T < (h : ℝ)}
  have hi : Integrable (E.indicator (fun _ => (m : ℝ))) (Forward.heightLaw allAttach m) :=
    (integrable_const _).indicator (by measurability)
  have hp : ∀ᵐ h : ℕ ∂Forward.heightLaw allAttach m,
      max ((h : ℝ) - T) 0 ≤ E.indicator (fun _ => (m : ℝ)) h := by
    filter_upwards [heightLaw_ae_le_edges m] with h hh
    have hh' : (h : ℝ) ≤ m := by exact_mod_cast hh
    by_cases he : h ∈ E
    · rw [Set.indicator_of_mem he]
      apply max_le
      · linarith
      · exact Nat.cast_nonneg _
    · rw [Set.indicator_of_notMem he]
      have ht : (h : ℝ) ≤ T := by
        change ¬T < (h : ℝ) at he
        exact le_of_not_gt he
      exact max_le (sub_nonpos.mpr ht) le_rfl
  have hmono := integral_mono_ae (upperExcessAt_integrable m T) hi hp
  rw [integral_indicator_const _ (by measurability), smul_eq_mul] at hmono
  simpa only [upperExcessAt, E, mul_comm] using hmono

theorem lowerTail_antitone_time {k l : ℕ} (hkl : k ≤ l) (T : ℝ) :
    lowerTail l T ≤ lowerTail k T := by
  let E : Set ℕ := {h | (h : ℝ) < T}
  let f : ℕ → ℝ := E.indicator (fun _ => 1)
  have hf : Antitone f := by
    intro a b hab
    by_cases hb : b ∈ E
    · have ha : a ∈ E := by
        change (a : ℝ) < T
        exact lt_of_le_of_lt (Nat.cast_le.mpr hab) (show (b : ℝ) < T from hb)
      simp only [f, Set.indicator_of_mem ha, Set.indicator_of_mem hb]
      exact le_rfl
    · rw [show f b = 0 from Set.indicator_of_notMem hb _]
      exact Set.indicator_nonneg (fun _ _ => by norm_num) _
  have hh := Forward.heightLaw_integral_antitone_time allAttach hkl f hf
  have hI (n : ℕ) : (∫ h, f h ∂Forward.heightLaw allAttach n) = lowerTail n T :=
    integral_indicator_one (by measurability : MeasurableSet E)
  rw [hI l, hI k] at hh
  exact hh

end RRT

namespace RRTSplit

theorem heightPairLaw_max_lowerTail_le (n : ℕ) (T : ℝ) :
    (heightPairLaw n).real {p | (max p.1 p.2 : ℕ) < T} ≤ RRT.lowerTail (n / 2) T := by
  let E : Set ℕ := {h | (h : ℝ) < T}
  have he : {p : ℕ × ℕ | (max p.1 p.2 : ℕ) < T} = E ×ˢ E := by
    ext p
    simp only [Nat.cast_max, max_lt_iff, Set.mem_ofPred_eq, Set.mem_prod, E]
  rw [he, heightPairLaw_real_rectangle]
  change 1 / ((n : ℝ) + 1) * ∑ k ∈ Finset.range (n + 1),
    RRT.lowerTail k T * RRT.lowerTail (n - k) T ≤ _
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      RRT.lowerTail k T * RRT.lowerTail (n - k) T ≤ RRT.lowerTail (n / 2) T := by
    have hk' := Finset.mem_range.mp hk
    by_cases hl : n / 2 ≤ k
    · simpa only [mul_one] using mul_le_mul
        (RRT.lowerTail_antitone_time hl T) (RRT.lowerTail_le_one (n - k) T)
        (RRT.lowerTail_nonneg (n - k) T) (RRT.lowerTail_nonneg (n / 2) T)
    · have hr : n / 2 ≤ n - k := by omega
      simpa only [one_mul] using mul_le_mul (RRT.lowerTail_le_one k T)
        (RRT.lowerTail_antitone_time hr T) (RRT.lowerTail_nonneg (n - k) T)
        (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ 1 / ((n : ℝ) + 1) * ∑ _k ∈ Finset.range (n + 1), RRT.lowerTail (n / 2) T :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = RRT.lowerTail (n / 2) T := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp

theorem splitDeficitAt_le_threshold_tail (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    splitDeficitAt n T ≤ T * RRT.lowerTail (n / 2) T := by
  let E : Set (ℕ × ℕ) := {p | (max p.1 p.2 : ℕ) < T}
  have hp (p : ℕ × ℕ) : max (T - (max p.1 p.2 : ℕ)) 0 ≤
      E.indicator (fun _ => T) p := by
    by_cases he : p ∈ E
    · rw [Set.indicator_of_mem he]
      apply max_le
      · have := Nat.cast_nonneg (α := ℝ) (max p.1 p.2)
        linarith
      · exact hT
    · rw [Set.indicator_of_notMem he]
      have ht : T ≤ ((max p.1 p.2 : ℕ) : ℝ) := by
        change ¬((max p.1 p.2 : ℕ) : ℝ) < T at he
        exact le_of_not_gt he
      exact max_le (sub_nonpos.mpr ht) le_rfl
  have hmono := integral_mono (heightPairLaw_integrable n _)
    ((integrable_const T).indicator (by measurability : MeasurableSet E)) hp
  rw [integral_indicator_const _ (by measurability), smul_eq_mul] at hmono
  calc
    splitDeficitAt n T ≤ T * (heightPairLaw n).real E := by
      simpa only [splitDeficitAt, mul_comm] using hmono
    _ ≤ T * RRT.lowerTail (n / 2) T :=
      mul_le_mul_of_nonneg_left (heightPairLaw_max_lowerTail_le n T) hT

/-- Finite-size residual estimate with an arbitrary nonnegative cutoff. -/
theorem residual_le_tail_bound (m n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    residual m n ≤ 2 * (m : ℝ) * Real.exp (RRT.upperComparisonCenter m - T) +
      T * RRT.lowerTail (n / 2) T := by
  apply (residual_le_upperExcessAt_add_splitDeficitAt m n T).trans
  apply add_le_add _ (splitDeficitAt_le_threshold_tail n hT)
  calc
    RRT.upperExcessAt m T ≤ (m : ℝ) *
        (Forward.heightLaw RRT.allAttach m).real {h | T < (h : ℝ)} :=
      RRT.upperExcessAt_le_support_tail m hT
    _ ≤ (m : ℝ) * (2 * Real.exp (RRT.upperComparisonCenter m - T)) :=
      mul_le_mul_of_nonneg_left (RRT.heightLaw_strict_upper_tail_exp m T) (Nat.cast_nonneg _)
    _ = _ := by ring

noncomputable def residualDecayRate : ℝ := 6 * Real.exp 1 - 16

theorem residualDecayRate_pos : 0 < residualDecayRate := by
  have := Real.exp_one_gt_d9
  unfold residualDecayRate
  linarith

theorem log_succ_le_log_add_log_two {m : ℕ} (hm : 1 ≤ m) :
    Real.log ((m : ℝ) + 1) ≤ Real.log (m : ℝ) + Real.log 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsmall : (m : ℝ) + 1 ≤ (m : ℝ) * 2 := by linarith
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < (m : ℝ) + 1)
    hsmall
  rwa [Real.log_mul hmpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh

theorem lowerCenter_half_coarse_log {m n : ℕ} (hm : 2 ≤ m) (hmn : m ^ 9 ≤ n) :
    8 * (Real.exp 1 - 2) * Real.log (m : ℝ) ≤ RRT.lowerCenter 2 (n / 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hpow : m ^ 8 ≤ n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    calc
      m ^ 8 * 2 ≤ m ^ 8 * m := Nat.mul_le_mul_left _ hm
      _ = m ^ 9 := (pow_succ m 8).symm
      _ ≤ n := hmn
  have hcast : (m : ℝ) ^ 8 ≤ ((n / 2 : ℕ) : ℝ) + 1 := by
    have hh : (m : ℝ) ^ 8 ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hpow
    linarith
  have hh := Real.log_le_log (pow_pos hmpos 8) hcast
  simp only [Real.log_pow, Nat.cast_ofNat] at hh
  have he : 0 ≤ Real.exp 1 - 2 := by have := Real.exp_one_gt_two; linarith
  have hbound := mul_le_mul_of_nonneg_left hh he
  exact (by nlinarith : 8 * (Real.exp 1 - 2) * Real.log (m : ℝ) ≤
    (Real.exp 1 - 2) * Real.log (((n / 2 : ℕ) : ℝ) + 1)).trans
      (RRT.lowerCenter_two_lower _)

noncomputable def residualUpperEnvelope (m : ℕ) : ℝ :=
  2 * Real.exp (Real.exp 1 * Real.log 2) *
    Real.exp ((1 - Real.exp 1) * Real.log ((m : ℝ) + 1))

noncomputable def residualLowerEnvelope (α B : ℝ) (m : ℕ) : ℝ :=
  2 * Real.exp 1 * (Real.log (m : ℝ) + Real.log 2) *
    Real.exp (α * (B + 2 * Real.exp 1 * Real.log 2 - residualDecayRate * Real.log (m : ℝ)))

theorem residual_upper_tail_envelope (m : ℕ) :
    2 * (m : ℝ) * Real.exp (RRT.upperComparisonCenter m -
      2 * Real.exp 1 * Real.log ((m : ℝ) + 1)) ≤ residualUpperEnvelope m := by
  let b := Real.log ((m : ℝ) + 1)
  have hc : RRT.upperComparisonCenter m - 2 * Real.exp 1 * b =
      Real.exp 1 * Real.log 2 - Real.exp 1 * b := by
    rw [RRT.upperComparisonCenter_eq]
    dsimp [b]
    ring
  have he : ((m : ℝ) + 1) * Real.exp (Real.exp 1 * Real.log 2 - Real.exp 1 * b) =
      Real.exp (Real.exp 1 * Real.log 2) * Real.exp ((1 - Real.exp 1) * b) := by
    calc
      _ = Real.exp b * Real.exp (Real.exp 1 * Real.log 2 - Real.exp 1 * b) := by
        rw [show Real.exp b = (m : ℝ) + 1 from Real.exp_log (by positivity)]
      _ = Real.exp (b + (Real.exp 1 * Real.log 2 - Real.exp 1 * b)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (Real.exp 1 * Real.log 2 + (1 - Real.exp 1) * b) := by congr 1; ring
      _ = _ := Real.exp_add _ _
  change 2 * (m : ℝ) * Real.exp (RRT.upperComparisonCenter m - 2 * Real.exp 1 * b) ≤ _
  rw [hc]
  calc
    _ ≤ 2 * (((m : ℝ) + 1) * Real.exp (Real.exp 1 * Real.log 2 - Real.exp 1 * b)) := by
      nlinarith [Real.exp_pos (Real.exp 1 * Real.log 2 - Real.exp 1 * b)]
    _ = residualUpperEnvelope m := by rw [he]; unfold residualUpperEnvelope; dsimp [b]; ring

theorem residual_lower_tail_envelope {α B : ℝ} (hα : 0 < α)
    (htail : ∀ n : ℕ, ∀ r : ℝ,
      RRT.lowerTail n r ≤ Real.exp (α * (B + r - RRT.lowerCenter 2 n)))
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ^ 9 ≤ n) :
    (2 * Real.exp 1 * Real.log ((m : ℝ) + 1)) *
      RRT.lowerTail (n / 2) (2 * Real.exp 1 * Real.log ((m : ℝ) + 1)) ≤
        residualLowerEnvelope α B m := by
  let T := 2 * Real.exp 1 * Real.log ((m : ℝ) + 1)
  let P := 2 * Real.exp 1 * (Real.log (m : ℝ) + Real.log 2)
  have hT : 0 ≤ T := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ (m : ℝ) + 1 by
      have := Nat.cast_nonneg (α := ℝ) m; linarith)
    dsimp [T]
    positivity
  have hTP : T ≤ P :=
    mul_le_mul_of_nonneg_left (log_succ_le_log_add_log_two (by omega)) (by positivity)
  have hP : 0 ≤ P := hT.trans hTP
  have hcenter := lowerCenter_half_coarse_log hm hmn
  have harg : B + T - RRT.lowerCenter 2 (n / 2) ≤
      B + 2 * Real.exp 1 * Real.log 2 - residualDecayRate * Real.log (m : ℝ) := by
    dsimp [T, P, residualDecayRate] at *
    nlinarith
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left harg hα.le)
  calc
    T * RRT.lowerTail (n / 2) T ≤ T * Real.exp (α * (B + T - RRT.lowerCenter 2 (n / 2))) :=
      mul_le_mul_of_nonneg_left (htail _ _) hT
    _ ≤ P * Real.exp (α * (B + 2 * Real.exp 1 * Real.log 2 -
        residualDecayRate * Real.log (m : ℝ))) :=
      mul_le_mul hTP he (Real.exp_pos _).le hP
    _ = residualLowerEnvelope α B m := rfl

/-- A single envelope in `m` controls every suffix `n ≥ m^9`. -/
theorem residual_le_decay_envelope {α B : ℝ} (hα : 0 < α)
    (htail : ∀ n : ℕ, ∀ r : ℝ,
      RRT.lowerTail n r ≤ Real.exp (α * (B + r - RRT.lowerCenter 2 n)))
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ^ 9 ≤ n) :
    residual m n ≤ residualUpperEnvelope m + residualLowerEnvelope α B m := by
  have hT : 0 ≤ 2 * Real.exp 1 * Real.log ((m : ℝ) + 1) := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ (m : ℝ) + 1 by
      have := Nat.cast_nonneg (α := ℝ) m; linarith)
    positivity
  exact (residual_le_tail_bound m n hT).trans
    (add_le_add (residual_upper_tail_envelope m) (residual_lower_tail_envelope hα htail hm hmn))

theorem tendsto_residualUpperEnvelope : Tendsto residualUpperEnvelope atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => 2 * Real.exp (Real.exp 1 * Real.log 2) *
    Real.exp ((1 - Real.exp 1) * Real.log ((m : ℝ) + 1))) atTop (𝓝 0)
  simpa only [mul_zero] using
    tendsto_upper_residual_exp_decay.const_mul (2 * Real.exp (Real.exp 1 * Real.log 2))

theorem tendsto_residualLowerEnvelope {α B : ℝ} (hα : 0 < α) :
    Tendsto (residualLowerEnvelope α B) atTop (𝓝 0) := by
  have hh := (tendsto_log_exp_decay α residualDecayRate (B + 2 * Real.exp 1 * Real.log 2)
    hα residualDecayRate_pos).const_mul (2 * Real.exp 1)
  change Tendsto (fun m : ℕ => 2 * Real.exp 1 * (Real.log (m : ℝ) + Real.log 2) *
    Real.exp (α * (B + 2 * Real.exp 1 * Real.log 2 - residualDecayRate * Real.log (m : ℝ))))
      atTop (𝓝 0)
  simpa only [mul_assoc, mul_zero] using hh

/-- The actual residual tends to zero uniformly over all suffixes at least the
ninth power of the old-tree size. The positive lower-tail rate is proved. -/
theorem residual_uniform_tendsto_zero :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, m ^ 9 ≤ n → residual m n ≤ ε := by
  obtain ⟨α, B, hα, _, htail⟩ := RRT.uniformLowerTailExponential
  have hlim : Tendsto (fun m => residualUpperEnvelope m + residualLowerEnvelope α B m)
      atTop (𝓝 0) := by
    simpa only [add_zero] using tendsto_residualUpperEnvelope.add (tendsto_residualLowerEnvelope hα)
  intro ε hε
  have hsmall := (tendsto_order.mp hlim).2 ε hε
  filter_upwards [eventually_ge_atTop 2, hsmall] with m hm hsmall
  intro n hmn
  exact (residual_le_decay_envelope hα htail hm hmn).trans hsmall.le

end RRTSplit
end FreezingGrowth
