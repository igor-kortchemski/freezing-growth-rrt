module

public import FreezingGrowth.RRTSplitRoughGap
public import FreezingGrowth.ForwardFiniteSupport

/-!
# A uniform residual bound for an old tree and a later component pair

The old height and the split pair have their actual product law. Decreasing
height tests are compared by actual one-step growth, and the larger split
component bounds the lower residual. No sharp height estimate is assumed.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

namespace Forward

theorem heightLaw_integral_antitone_succ (x : SignSequence) (n : ℕ)
    (f : ℕ → ℝ) (hf : Antitone f) :
    (∫ h, f h ∂heightLaw x (n + 1)) ≤ ∫ h, f h ∂heightLaw x n := by
  rw [heightLaw_integral, treeLaw_integral_succ_state, heightLaw_integral]
  apply integral_mono_ae (treeLaw_integrable_state x n _)
    (treeLaw_integrable_heightTest x n f)
  filter_upwards [treeLaw_valid x n] with s hs
  by_cases ha : s.active.Nonempty
  · rw [transitionLaw_integral s _ _ ha]
    apply (div_le_iff₀ (by exact_mod_cast ha.card_pos : (0 : ℝ) < s.active.card)).mpr
    have hh := Finset.sum_le_sum (s := s.active)
      (fun v _ => hf (treeHeight_le_step hs (x (n + 1)) v))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hh
  · simp [transitionLaw, ha]

theorem heightLaw_integral_antitone_time (x : SignSequence) {n m : ℕ}
    (hnm : n ≤ m) (f : ℕ → ℝ) (hf : Antitone f) :
    (∫ h, f h ∂heightLaw x m) ≤ ∫ h, f h ∂heightLaw x n := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (heightLaw_integral_antitone_succ x m f hf).trans ih

end Forward

namespace RRTSplit

theorem antitone_height_deficit (T : ℝ) :
    Antitone (fun h : ℕ => max (T - (h : ℝ)) 0) := by
  intro a b hab
  exact max_le_max (sub_le_sub_left (Nat.cast_le.mpr hab) T) le_rfl

theorem heightProduct_deficit_integrable (k l : ℕ) (T : ℝ) :
    Integrable (fun p : ℕ × ℕ => max (T - (max p.1 p.2 : ℕ)) 0)
      ((Forward.heightLaw RRT.allAttach k).prod (Forward.heightLaw RRT.allAttach l)) := by
  apply (integrable_const (max T 0)).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  apply max_le_max _ le_rfl
  have := Nat.cast_nonneg (α := ℝ) (max p.1 p.2)
  linarith

theorem integral_heightProduct_deficit_le_left (k l : ℕ) (T : ℝ) :
    (∫ p : ℕ × ℕ, max (T - (max p.1 p.2 : ℕ)) 0
      ∂(Forward.heightLaw RRT.allAttach k).prod (Forward.heightLaw RRT.allAttach l)) ≤
        ∫ h : ℕ, max (T - (h : ℝ)) 0 ∂Forward.heightLaw RRT.allAttach k := by
  have hi := (Forward.heightLaw_integrable RRT.allAttach k
    (fun h : ℕ => max (T - (h : ℝ)) 0)).comp_fst
      (Forward.heightLaw RRT.allAttach l)
  calc
    _ ≤ ∫ p : ℕ × ℕ, max (T - (p.1 : ℝ)) 0
        ∂(Forward.heightLaw RRT.allAttach k).prod (Forward.heightLaw RRT.allAttach l) := by
      apply integral_mono (heightProduct_deficit_integrable k l T) hi
      intro p
      exact antitone_height_deficit T (le_max_left _ _)
    _ = _ := by
      rw [← integral_map (f := fun h : ℕ => max (T - (h : ℝ)) 0)
        measurable_fst.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
      simp

theorem integral_heightProduct_deficit_le_right (k l : ℕ) (T : ℝ) :
    (∫ p : ℕ × ℕ, max (T - (max p.1 p.2 : ℕ)) 0
      ∂(Forward.heightLaw RRT.allAttach k).prod (Forward.heightLaw RRT.allAttach l)) ≤
        ∫ h : ℕ, max (T - (h : ℝ)) 0 ∂Forward.heightLaw RRT.allAttach l := by
  have hi := (Forward.heightLaw_integrable RRT.allAttach l
    (fun h : ℕ => max (T - (h : ℝ)) 0)).comp_snd
      (Forward.heightLaw RRT.allAttach k)
  calc
    _ ≤ ∫ p : ℕ × ℕ, max (T - (p.2 : ℝ)) 0
        ∂(Forward.heightLaw RRT.allAttach k).prod (Forward.heightLaw RRT.allAttach l) := by
      apply integral_mono (heightProduct_deficit_integrable k l T) hi
      intro p
      exact antitone_height_deficit T (le_max_right _ _)
    _ = _ := by
      rw [← integral_map (f := fun h : ℕ => max (T - (h : ℝ)) 0)
        measurable_snd.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
      simp

noncomputable def splitDeficitAt (n : ℕ) (T : ℝ) : ℝ :=
  ∫ p : ℕ × ℕ, max (T - (max p.1 p.2 : ℕ)) 0 ∂heightPairLaw n

/-- At least one component has at least half of the remaining edges. -/
theorem splitDeficitAt_le (n : ℕ) (T : ℝ) :
    splitDeficitAt n T ≤
      ∫ h : ℕ, max (T - (h : ℝ)) 0 ∂Forward.heightLaw RRT.allAttach (n / 2) := by
  let D := ∫ h : ℕ, max (T - (h : ℝ)) 0 ∂Forward.heightLaw RRT.allAttach (n / 2)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (∫ p : ℕ × ℕ, max (T - (max p.1 p.2 : ℕ)) 0
        ∂(Forward.heightLaw RRT.allAttach k).prod
          (Forward.heightLaw RRT.allAttach (n - k))) ≤ D := by
    have hk' := Finset.mem_range.mp hk
    by_cases hlarge : n / 2 ≤ k
    · exact (integral_heightProduct_deficit_le_left k (n - k) T).trans
        (Forward.heightLaw_integral_antitone_time RRT.allAttach hlarge _
          (antitone_height_deficit T))
    · have hlarge' : n / 2 ≤ n - k := by omega
      exact (integral_heightProduct_deficit_le_right k (n - k) T).trans
        (Forward.heightLaw_integral_antitone_time RRT.allAttach hlarge' _
          (antitone_height_deficit T))
  rw [splitDeficitAt, heightPairLaw_eq_sum, integral_smul_measure,
    integral_finsetSum_measure (fun k _ => heightProduct_deficit_integrable k (n - k) T)]
  simp only [ENNReal.toReal_inv, Nat.cast_add, Nat.cast_one, smul_eq_mul]
  calc
    _ ≤ ((n : ℝ) + 1)⁻¹ * ∑ _k ∈ Finset.range (n + 1), D :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = D := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp

noncomputable def oldSplitHeightLaw (m n : ℕ) : Measure (ℕ × (ℕ × ℕ)) :=
  (Forward.heightLaw RRT.allAttach m).prod (heightPairLaw n)

instance oldSplitHeightLaw_probability (m n : ℕ) :
    IsProbabilityMeasure (oldSplitHeightLaw m n) :=
  inferInstanceAs (IsProbabilityMeasure
    ((Forward.heightLaw RRT.allAttach m).prod (heightPairLaw n)))

noncomputable def residual (m n : ℕ) : ℝ :=
  ∫ z : ℕ × (ℕ × ℕ), max ((z.1 : ℝ) - (max z.2.1 z.2.2 : ℕ)) 0
    ∂oldSplitHeightLaw m n

theorem residual_integrable (m n : ℕ) :
    Integrable (fun z : ℕ × (ℕ × ℕ) =>
      max ((z.1 : ℝ) - (max z.2.1 z.2.2 : ℕ)) 0) (oldSplitHeightLaw m n) := by
  have hi := (Forward.heightLaw_integrable RRT.allAttach m (fun h : ℕ => (h : ℝ))).comp_fst
    (heightPairLaw n)
  apply hi.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · have := Nat.cast_nonneg (α := ℝ) (max z.2.1 z.2.2)
    linarith
  · exact Nat.cast_nonneg _

theorem residual_nonneg (m n : ℕ) : 0 ≤ residual m n :=
  integral_nonneg (fun _ => le_max_right _ _)

/-- Fubini on the genuine old-height and future-split product law. -/
theorem residual_eq_integral_splitDeficitAt (m n : ℕ) :
    residual m n = ∫ h : ℕ, splitDeficitAt n (h : ℝ)
      ∂Forward.heightLaw RRT.allAttach m := by
  rw [residual, oldSplitHeightLaw, integral_prod _ (residual_integrable m n)]
  rfl

theorem residual_eq_treeIntegral_splitDeficitAt (m n : ℕ) :
    residual m n = ∫ s, splitDeficitAt n (Forward.treeHeight s : ℝ)
      ∂Forward.treeLaw RRT.allAttach m := by
  rw [residual_eq_integral_splitDeficitAt, Forward.heightLaw_integral]

theorem residual_le_upperExcessAt_add_splitDeficitAt (m n : ℕ) (T : ℝ) :
    residual m n ≤ RRT.upperExcessAt m T + splitDeficitAt n T := by
  have hu := (RRT.upperExcessAt_integrable m T).comp_fst (heightPairLaw n)
  have hl := (heightPairLaw_integrable n
    (fun p => max (T - (max p.1 p.2 : ℕ)) 0)).comp_snd (Forward.heightLaw RRT.allAttach m)
  have hp (z : ℕ × (ℕ × ℕ)) :
      max ((z.1 : ℝ) - (max z.2.1 z.2.2 : ℕ)) 0 ≤
        max ((z.1 : ℝ) - T) 0 + max (T - (max z.2.1 z.2.2 : ℕ)) 0 := by
    have h1 := le_max_left ((z.1 : ℝ) - T) 0
    have h2 := le_max_left (T - (max z.2.1 z.2.2 : ℕ)) 0
    have h3 := le_max_right ((z.1 : ℝ) - T) 0
    have h4 := le_max_right (T - (max z.2.1 z.2.2 : ℕ)) 0
    apply max_le <;> linarith
  calc
    residual m n ≤ ∫ z : ℕ × (ℕ × ℕ),
        (max ((z.1 : ℝ) - T) 0 + max (T - (max z.2.1 z.2.2 : ℕ)) 0)
          ∂oldSplitHeightLaw m n := integral_mono (residual_integrable m n) (hu.add hl) hp
    _ = RRT.upperExcessAt m T + splitDeficitAt n T := by
      have hAdd := integral_add hu hl
      change (∫ z : ℕ × (ℕ × ℕ),
        (max ((z.1 : ℝ) - T) 0 + max (T - (max z.2.1 z.2.2 : ℕ)) 0)
          ∂(Forward.heightLaw RRT.allAttach m).prod (heightPairLaw n)) = _
      rw [hAdd]
      congr 1
      · rw [← integral_map (f := fun h : ℕ => max ((h : ℝ) - T) 0)
          measurable_fst.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
        simp [RRT.upperExcessAt]
      · rw [← integral_map
          (f := fun p : ℕ × ℕ => max (T - (max p.1 p.2 : ℕ)) 0)
          measurable_snd.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
        simp [splitDeficitAt]

/-- A center separation supplies a bounded residual without requiring a sharp
tail rate or a vanishing-residual theorem. -/
theorem residual_le_excess_add_deficit (m n : ℕ)
    (hcenter : Real.exp 1 * Real.log ((m : ℝ) + 1) ≤ RRT.lowerCenter 2 (n / 2)) :
    residual m n ≤ RRT.upperExcess m + RRT.lowerDeficit 2 (n / 2) := by
  apply (residual_le_upperExcessAt_add_splitDeficitAt m n (RRT.lowerCenter 2 (n / 2))).trans
  apply add_le_add
  · apply integral_mono (RRT.upperExcessAt_integrable m _)
      (RRT.upperExcessAt_integrable m _)
    intro h
    exact max_le_max (sub_le_sub_left hcenter _) le_rfl
  · exact splitDeficitAt_le n _

theorem uniformResidualBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ,
      Real.exp 1 * Real.log ((m : ℝ) + 1) ≤ RRT.lowerCenter 2 (n / 2) →
        residual m n ≤ C := by
  obtain ⟨D, hD, hd⟩ := RRT.uniformLowerDeficit_of_seed (by norm_num : (0 : ℝ) ≤ 2)
    (RRT.constantSuccessSeed_of_clockLowerSeed PWIT.clockLowerSeed)
  refine ⟨RRT.upperExcessConstant + D, add_nonneg RRT.upperExcessConstant_pos.le hD,
    fun m n hc => ?_⟩
  exact (residual_le_excess_add_deficit m n hc).trans
    (add_le_add (RRT.upperExcess_le m) (hd (n / 2)))

/-- The ninth-power scale has ample deterministic separation already at every
`m ≥ 2`; no limiting comparison of rounded indices is needed. -/
theorem lowerCenter_half_pow_nine_ge {m : ℕ} (hm : 2 ≤ m) :
    Real.exp 1 * Real.log ((m : ℝ) + 1) ≤ RRT.lowerCenter 2 (m ^ 9 / 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hln : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hpow : m ^ 8 ≤ m ^ 9 / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    calc
      m ^ 8 * 2 ≤ m ^ 8 * m := Nat.mul_le_mul_left _ hm
      _ = m ^ 9 := (pow_succ m 8).symm
  have hsmall : (m : ℝ) + 1 ≤ (m : ℝ) ^ 2 := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hlogsmall : Real.log ((m : ℝ) + 1) ≤ 2 * Real.log (m : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (m : ℝ) + 1) hsmall
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hloglarge : 8 * Real.log (m : ℝ) ≤ Real.log ((m ^ 9 / 2 : ℕ) + (1 : ℝ)) := by
    have hcast : (m : ℝ) ^ 8 ≤ ((m ^ 9 / 2 : ℕ) : ℝ) + 1 := by
      have hh : (m : ℝ) ^ 8 ≤ ((m ^ 9 / 2 : ℕ) : ℝ) := by exact_mod_cast hpow
      linarith
    have hh := Real.log_le_log (pow_pos hmpos 8) hcast
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have he : 0 ≤ Real.exp 1 - 2 := by have := Real.exp_one_gt_two; linarith
  have hcoef : 2 * Real.exp 1 ≤ 8 * (Real.exp 1 - 2) := by
    have := Real.exp_one_gt_d9
    linarith
  calc
    Real.exp 1 * Real.log ((m : ℝ) + 1) ≤
        Real.exp 1 * (2 * Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogsmall (Real.exp_pos _).le
    _ ≤ (Real.exp 1 - 2) * (8 * Real.log (m : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef hln]
    _ ≤ (Real.exp 1 - 2) * Real.log ((m ^ 9 / 2 : ℕ) + (1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hloglarge he
    _ ≤ RRT.lowerCenter 2 (m ^ 9 / 2) := RRT.lowerCenter_two_lower _

theorem uniformResidualBound_pow_nine :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m → residual m (m ^ 9) ≤ C := by
  obtain ⟨C, hC, hres⟩ := uniformResidualBound
  exact ⟨C, hC, fun m hm => hres m (m ^ 9) (lowerCenter_half_pow_nine_ge hm)⟩

end RRTSplit
end FreezingGrowth
