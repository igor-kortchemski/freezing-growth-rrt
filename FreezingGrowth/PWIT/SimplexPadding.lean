module

public import FreezingGrowth.PWIT.GammaWindows
public import FreezingGrowth.PWIT.SimplexGrouped

/-!
# Quantitative three-block padding for the simplex bridge

The rectangle is obtained from independent Gamma block totals and then
normalized by their actual sum. No independence after fixing that sum is
asserted. The barrier parameter is real; integer block lengths are supplied
with explicit rounding bounds.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem padding_normalization_error {a n N T z : ℝ}
    (ha : 0 ≤ a) (hn : 0 < n) (hsqrt : 36 * a ≤ Real.sqrt n)
    (hT : n / 2 ≤ T) (hz : 0 ≤ z) (hzu : z ≤ 3 * a ^ 2)
    (hdelta : |T - N| ≤ 2 * Real.sqrt n) :
    |N / T * z - z| ≤ a / 3 := by
  have hTp : 0 < T := lt_of_lt_of_le (half_pos hn) hT
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hs2 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  have he : N / T * z - z = (N - T) * z / T := by field_simp
  rw [he, abs_div, abs_mul, abs_of_nonneg hz, abs_of_pos hTp, abs_sub_comm]
  calc
    _ ≤ ((2 * Real.sqrt n) * (3 * a ^ 2)) / T :=
      div_le_div_of_nonneg_right (mul_le_mul hdelta hzu hz (by positivity)) hTp.le
    _ ≤ ((2 * Real.sqrt n) * (3 * a ^ 2)) / (n / 2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos hn) hT
    _ = 12 * a ^ 2 / Real.sqrt n := by
      field_simp
      nlinarith
    _ ≤ a / 3 := by
      apply (div_le_iff₀ hsp).mpr
      have hmul := mul_le_mul_of_nonneg_right hsqrt ha
      nlinarith

theorem padding_scale_bounds {a n : ℝ} (ha : 10 ≤ a) (hn : a ^ 6 ≤ n) :
    0 < n ∧ a ^ 3 ≤ Real.sqrt n ∧ 36 * a ≤ Real.sqrt n ∧ 4 ≤ Real.sqrt n := by
  have hap : 0 < a := by linarith
  have ha2 : 100 ≤ a ^ 2 := by nlinarith
  have ha3 : 36 * a ≤ a ^ 3 := by
    have h := mul_nonneg hap.le (show 0 ≤ a ^ 2 - 36 by linarith)
    nlinarith
  have hnp : 0 < n := lt_of_lt_of_le (pow_pos hap 6) hn
  have has : a ^ 3 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by nlinarith [hn])
  refine ⟨hnp, has, ha3.trans has, ?_⟩
  linarith [ha3.trans has]

/-- Normalization sends the independent off-center Gamma windows to the
joint rectangle required by the near-leading padding argument. -/
theorem simplex_padding_rectangle {a m n z₁ z₂ z₃ : ℝ}
    (ha : 10 ≤ a) (hm : a ^ 2 ≤ m) (hm' : m ≤ a ^ 2 + 1) (hn : a ^ 6 ≤ n)
    (hz₁ : z₁ ∈ Icc (m + 4 * a / 3) (m + 5 * a / 3))
    (hz₂ : z₂ ∈ Icc (m - 8 * a / 3) (m - 7 * a / 3))
    (hz₃ : z₃ ∈ Icc (n - Real.sqrt n) (n + Real.sqrt n)) :
    0 < z₁ + z₂ + z₃ ∧
      (n + 2 * m) / (z₁ + z₂ + z₃) * z₁ ∈ Icc (m + a) (m + 2 * a) ∧
      (n + 2 * m) / (z₁ + z₂ + z₃) * z₂ ∈ Icc (m - 3 * a) (m - 2 * a) := by
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 100 ≤ a ^ 2 := by nlinarith
  obtain ⟨hnp, _, has, hs4⟩ := padding_scale_bounds ha hn
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hnp.le
  obtain ⟨hz₁l, hz₁u⟩ := hz₁
  obtain ⟨hz₂l, hz₂u⟩ := hz₂
  obtain ⟨hz₃l, hz₃u⟩ := hz₃
  have hz₁0 : 0 ≤ z₁ := by nlinarith
  have hz₂0 : 0 ≤ z₂ := by nlinarith
  have hz₁b : z₁ ≤ 3 * a ^ 2 := by nlinarith
  have hz₂b : z₂ ≤ 3 * a ^ 2 := by nlinarith
  have hdelta : |(z₁ + z₂ + z₃) - (n + 2 * m)| ≤ 2 * Real.sqrt n := by
    apply abs_le.mpr
    constructor <;> linarith
  have hT : n / 2 ≤ z₁ + z₂ + z₃ := by
    have hmd : 0 ≤ m := le_trans (sq_nonneg a) hm
    have hh := (abs_le.mp hdelta).1
    nlinarith
  have hTp : 0 < z₁ + z₂ + z₃ := lt_of_lt_of_le (half_pos hnp) hT
  have he₁ := abs_le.mp (padding_normalization_error ha0 hnp has hT hz₁0 hz₁b hdelta)
  have he₂ := abs_le.mp (padding_normalization_error ha0 hnp has hT hz₂0 hz₂b hdelta)
  refine ⟨hTp, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- The integer mode of either short padding block is comparable to `a²`.
The weaker factor `3/4` leaves ample room for the unit shape-to-mode shift. -/
theorem padding_side_mode_bounds {a : ℝ} {q : ℕ} (ha : 10 ≤ a)
    (hql : a ^ 2 ≤ (q : ℝ) + 1) (hqu : (q : ℝ) + 1 ≤ a ^ 2 + 1) :
    0 < q ∧ (64 : ℝ) ≤ q ∧ 3 * a / 4 ≤ Real.sqrt q ∧ Real.sqrt q ≤ a := by
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 100 ≤ a ^ 2 := by nlinarith
  have hq64 : (64 : ℝ) ≤ q := by linarith
  have hq : 0 < q := by exact_mod_cast (by linarith : (0 : ℝ) < q)
  refine ⟨hq, hq64, ?_, ?_⟩
  · exact Real.le_sqrt_of_sq_le (by nlinarith)
  · exact (Real.sqrt_le_iff).mpr ⟨ha0, by linarith⟩

theorem padding_gamma_side_window {a : ℝ} {q : ℕ} (ha : 10 ≤ a)
    (hql : a ^ 2 ≤ (q : ℝ) + 1) (hqu : (q : ℝ) + 1 ≤ a ^ 2 + 1)
    {l u : ℝ} (hl : -(8 * a / 3) ≤ l) (hu : u ≤ 5 * a / 3)
    (hwidth : u - l = a / 3) :
    Real.exp (-33) / 3 ≤ (gammaMeasure ((q : ℝ) + 1) 1).real
      (Icc ((q : ℝ) + 1 + l) ((q : ℝ) + 1 + u)) := by
  obtain ⟨hq, hq64, hsqlo, hsqup⟩ := padding_side_mode_bounds ha hql hqu
  have hap : 0 < a := by linarith
  have hsp : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hq)
  have hpdf : ∀ x ∈ Icc ((q : ℝ) + 1 + l) ((q : ℝ) + 1 + u),
      Real.exp (-33) / a ≤ gammaPDFReal ((q : ℝ) + 1) 1 x := by
    intro x hx
    obtain ⟨hxl, hxu⟩ := hx
    have hxdev : |x - q| ≤ 4 * Real.sqrt q := by
      apply abs_le.mpr
      constructor <;> linarith
    have h := gammaPDFReal_nat_succ_lower_window hq (C := 4) (by norm_num)
      (by norm_num at hq64 ⊢; exact hq64) hxdev
    norm_num only at h
    exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hsp hsqup).trans h
  have hb : (q : ℝ) + 1 + l ≤ (q : ℝ) + 1 + u := by linarith
  have h := gammaMeasure_nat_succ_window_lower_of_density q hb (by positivity) hpdf
  have he : Real.exp (-33) / a * (((q : ℝ) + 1 + u) - ((q : ℝ) + 1 + l)) =
      Real.exp (-33) / 3 := by
    rw [show ((q : ℝ) + 1 + u) - ((q : ℝ) + 1 + l) = u - l by ring, hwidth]
    field_simp
  rwa [he] at h

theorem padding_gamma_first_window {a : ℝ} {m : ℕ} (ha : 10 ≤ a)
    (hm : a ^ 2 ≤ (m : ℝ)) (hm' : (m : ℝ) ≤ a ^ 2 + 1) :
    Real.exp (-33) / 3 ≤ (gammaMeasure (m : ℝ) 1).real
      (Icc ((m : ℝ) + 4 * a / 3) ((m : ℝ) + 5 * a / 3)) := by
  cases m with
  | zero => norm_num at hm; nlinarith
  | succ q =>
    simp only [Nat.cast_add, Nat.cast_one] at hm hm' ⊢
    exact padding_gamma_side_window ha hm hm' (by linarith) le_rfl (by ring)

theorem padding_gamma_second_window {a : ℝ} {m : ℕ} (ha : 10 ≤ a)
    (hm : a ^ 2 ≤ (m : ℝ)) (hm' : (m : ℝ) ≤ a ^ 2 + 1) :
    Real.exp (-33) / 3 ≤ (gammaMeasure (m : ℝ) 1).real
      (Icc ((m : ℝ) - 8 * a / 3) ((m : ℝ) - 7 * a / 3)) := by
  cases m with
  | zero => norm_num at hm; nlinarith
  | succ q =>
    simp only [Nat.cast_add, Nat.cast_one] at hm hm' ⊢
    convert padding_gamma_side_window ha hm hm' (l := -(8 * a / 3))
      (u := -(7 * a / 3)) le_rfl (by linarith) (by ring) using 1

theorem padding_gamma_middle_window {n : ℕ} (hn : 17 ≤ n) :
    2 * Real.exp (-9) ≤ (gammaMeasure (n : ℝ) 1).real
      (Icc ((n : ℝ) - Real.sqrt n) ((n : ℝ) + Real.sqrt n)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hq16 : (16 : ℝ) ≤ q := by exact_mod_cast (by omega : 16 ≤ q)
  have hq : 0 < q := by omega
  have hqp : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqp
  have ht : 0 < Real.sqrt ((q : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt hqp.le
  have ht2 := Real.sq_sqrt (show 0 ≤ (q : ℝ) + 1 by positivity)
  have hs4 : 4 ≤ Real.sqrt (q : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hst : Real.sqrt (q : ℝ) ≤ Real.sqrt ((q : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hts : Real.sqrt ((q : ℝ) + 1) + 1 ≤ 2 * Real.sqrt (q : ℝ) := by nlinarith
  simp only [Nat.cast_succ]
  have hpdf : ∀ x ∈ Icc ((q : ℝ) + 1 - Real.sqrt ((q : ℝ) + 1))
      ((q : ℝ) + 1 + Real.sqrt ((q : ℝ) + 1)),
      Real.exp (-9) / Real.sqrt ((q : ℝ) + 1) ≤ gammaPDFReal ((q : ℝ) + 1) 1 x := by
    intro x hx
    obtain ⟨hxl, hxu⟩ := hx
    have hdev : |x - q| ≤ 2 * Real.sqrt q := by
      apply abs_le.mpr
      constructor <;> linarith
    have h := gammaPDFReal_nat_succ_lower_window hq (C := 2) (by norm_num)
      (by norm_num at hq16 ⊢; exact hq16) hdev
    norm_num only at h
    exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hs hst).trans h
  have h := gammaMeasure_nat_succ_window_lower_of_density q
    (show (q : ℝ) + 1 - Real.sqrt ((q : ℝ) + 1) ≤
      (q : ℝ) + 1 + Real.sqrt ((q : ℝ) + 1) by linarith) (by positivity) hpdf
  have he : Real.exp (-9) / Real.sqrt ((q : ℝ) + 1) *
      (((q : ℝ) + 1 + Real.sqrt ((q : ℝ) + 1)) -
        ((q : ℝ) + 1 - Real.sqrt ((q : ℝ) + 1))) = 2 * Real.exp (-9) := by
    field_simp
    ring
  rwa [he] at h

/-- Keep the full normalized path inside every block together with its total.
This product identity is stronger than a law for the three totals alone. -/
theorem normalizedSpacings_three_block_joint_law (m n : ℕ) [NeZero m] [NeZero n] :
    ((finiteClockLaw m).prod ((finiteClockLaw m).prod (finiteClockLaw n))).map
        (fun x => ((normalizedSpacings x.1, totalWait x.1),
          ((normalizedSpacings x.2.1, totalWait x.2.1),
            (normalizedSpacings x.2.2, totalWait x.2.2)))) =
      ((simplexLaw m).prod (gammaMeasure (m : ℝ) 1)).prod
        (((simplexLaw m).prod (gammaMeasure (m : ℝ) 1)).prod
          ((simplexLaw n).prod (gammaMeasure (n : ℝ) 1))) := by
  rw [← normalizedSpacings_joint_law m, ← normalizedSpacings_joint_law n]
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rfl

noncomputable def paddingWindowConstant : ℝ :=
  (Real.exp (-33) / 3) ^ 2 * (2 * Real.exp (-9))

theorem paddingWindowConstant_pos : 0 < paddingWindowConstant := by
  unfold paddingWindowConstant
  positivity

/-- The three independent windows have a fixed positive probability. -/
theorem gamma_three_padding_windows {a : ℝ} {m n : ℕ} (ha : 10 ≤ a)
    (hm : a ^ 2 ≤ (m : ℝ)) (hm' : (m : ℝ) ≤ a ^ 2 + 1) (hn : 17 ≤ n) :
    paddingWindowConstant ≤
      ((gammaMeasure (m : ℝ) 1).prod
        ((gammaMeasure (m : ℝ) 1).prod (gammaMeasure (n : ℝ) 1))).real
          (Icc ((m : ℝ) + 4 * a / 3) ((m : ℝ) + 5 * a / 3) ×ˢ
            (Icc ((m : ℝ) - 8 * a / 3) ((m : ℝ) - 7 * a / 3) ×ˢ
              Icc ((n : ℝ) - Real.sqrt n) ((n : ℝ) + Real.sqrt n))) := by
  have hmp : (0 : ℝ) < m := by nlinarith
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have : IsProbabilityMeasure (gammaMeasure (m : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure hmp (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (n : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure hnp (by norm_num)
  rw [measureReal_prod_prod, measureReal_prod_prod]
  unfold paddingWindowConstant
  have h₁ := padding_gamma_first_window ha hm hm'
  have h₂ := padding_gamma_second_window ha hm hm'
  have h₃ := padding_gamma_middle_window hn
  calc
    _ = (Real.exp (-33) / 3) * ((Real.exp (-33) / 3) * (2 * Real.exp (-9))) := by ring
    _ ≤ _ := mul_le_mul h₁ (mul_le_mul h₂ h₃ (by positivity) measureReal_nonneg)
      (by positivity) measureReal_nonneg

/-- A positive joint rectangle probability for the normalized block totals.
The law is a product of three independent Gamma variables before normalization. -/
theorem gamma_normalized_padding_rectangle {a : ℝ} {m n : ℕ} (ha : 10 ≤ a)
    (hm : a ^ 2 ≤ (m : ℝ)) (hm' : (m : ℝ) ≤ a ^ 2 + 1) (hn : a ^ 6 ≤ (n : ℝ)) :
    paddingWindowConstant ≤
      ((gammaMeasure (m : ℝ) 1).prod
        ((gammaMeasure (m : ℝ) 1).prod (gammaMeasure (n : ℝ) 1))).real
          {z | 0 < z.1 + z.2.1 + z.2.2 ∧
            ((n : ℝ) + 2 * m) / (z.1 + z.2.1 + z.2.2) * z.1 ∈
              Icc ((m : ℝ) + a) ((m : ℝ) + 2 * a) ∧
            ((n : ℝ) + 2 * m) / (z.1 + z.2.1 + z.2.2) * z.2.1 ∈
              Icc ((m : ℝ) - 3 * a) ((m : ℝ) - 2 * a)} := by
  have hmp : (0 : ℝ) < m := by nlinarith
  have hnp := (padding_scale_bounds ha hn).1
  have hn17 : 17 ≤ n := by
    have hpow : (10 : ℝ) ^ 6 ≤ a ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
    exact_mod_cast (show (17 : ℝ) ≤ n by norm_num at hpow; linarith)
  have : IsProbabilityMeasure (gammaMeasure (m : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure hmp (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (n : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure hnp (by norm_num)
  apply (gamma_three_padding_windows ha hm hm' hn17).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro z hz
  exact simplex_padding_rectangle ha hm hm' hn hz.1 hz.2.1 hz.2.2

end FreezingGrowth.PWIT
