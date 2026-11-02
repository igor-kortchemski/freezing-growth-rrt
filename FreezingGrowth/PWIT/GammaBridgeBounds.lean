module

public import FreezingGrowth.PWIT.GammaWindows

/-! Uniform Gamma density and positive unit-band estimates for transferring
events between an actual exponential-clock vector and its normalized bridge.
The estimates include shape one and require no finite-size enumeration. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set

theorem gammaPDFReal_nat_succ_upper_shape (k : ℕ) (x : ℝ) :
    gammaPDFReal ((k : ℝ) + 1) 1 x ≤ 2 / Real.sqrt ((k : ℝ) + 1) := by
  by_cases hk : k = 0
  · subst k
    by_cases hx : 0 ≤ x
    · rw [gammaPDFReal_nat_succ_formula 0 hx]
      have he : Real.exp (-x) ≤ 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
      norm_num
      linarith
    · simp only [gammaPDFReal, ite_eq_right hx]
      positivity
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
    have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hkpos)
    have htpos : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hs : Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt (k : ℝ) := by
      have hs2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
      have ht2 := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
      nlinarith
    apply (gammaPDFReal_nat_succ_upper hkpos x).trans
    apply (div_le_div_iff₀ hspos htpos).mpr
    linarith

/-- A global bound, also valid on negative inputs where the density vanishes. -/
theorem gammaPDFReal_nat_upper {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    gammaPDFReal (n : ℝ) 1 x ≤ 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Nat.cast_succ] using gammaPDFReal_nat_succ_upper_shape k x

theorem gammaPDFReal_nat_succ_lower_unitBand (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) :
    Real.exp (-3) / Real.sqrt ((k : ℝ) + 1) ≤
      gammaPDFReal ((k : ℝ) + 1) 1 x := by
  by_cases hk : k = 0
  · subst k
    have hxpos : 0 ≤ x := by norm_num at hx; linarith [hx.1]
    rw [gammaPDFReal_nat_succ_formula 0 hxpos]
    norm_num
    norm_num at hx
    linarith [hx.2]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
    have hxpos : 0 < x := by linarith [hx.1]
    have hr : 1 ≤ x / (k : ℝ) := (le_div_iff₀ hkR).mpr (by linarith [hx.1])
    have hl : 0 ≤ Real.log (x / (k : ℝ)) := Real.log_nonneg hr
    have harg : -3 ≤ (k : ℝ) * Real.log (x / k) - x + k - 1 := by
      nlinarith [mul_nonneg hkR.le hl, hx.2]
    calc
      Real.exp (-3) / Real.sqrt ((k : ℝ) + 1) ≤ Real.exp (-3) / Real.sqrt k :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le
          (Real.sqrt_pos.mpr hkR) (Real.sqrt_le_sqrt (by linarith))
      _ ≤ Real.exp ((k : ℝ) * Real.log (x / k) - x + k - 1) / Real.sqrt k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr harg) (Real.sqrt_nonneg _)
      _ ≤ _ := gammaPDFReal_nat_succ_lower_logRatio hkpos hxpos

/-- The positive-mass total band used in the normalized-bridge argument. -/
theorem gammaMeasure_nat_unitBand_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-3) / Real.sqrt (n : ℝ) ≤
      (gammaMeasure (n : ℝ) 1).real (Icc (n : ℝ) ((n : ℝ) + 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hh := gammaMeasure_nat_succ_window_lower_of_density k
    (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith)
    (show 0 ≤ Real.exp (-3) / Real.sqrt ((k : ℝ) + 1) by positivity)
    (fun x hx => gammaPDFReal_nat_succ_lower_unitBand k hx)
  convert hh using 1 <;> push_cast <;> ring_nf

theorem exists_gammaPDFReal_nat_upper : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, gammaPDFReal (n : ℝ) 1 x ≤ C / Real.sqrt (n : ℝ) :=
  ⟨2, by norm_num, fun _ hn x => gammaPDFReal_nat_upper hn x⟩

theorem exists_gammaMeasure_nat_unitBand_lower : ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 1 ≤ n → c / Real.sqrt (n : ℝ) ≤
      (gammaMeasure (n : ℝ) 1).real (Icc (n : ℝ) ((n : ℝ) + 1)) :=
  ⟨Real.exp (-3), Real.exp_pos _, fun _ hn => gammaMeasure_nat_unitBand_lower hn⟩

end FreezingGrowth.PWIT
