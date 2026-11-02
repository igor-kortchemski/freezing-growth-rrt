module

public import FreezingGrowth.PWIT.LogBarrierGeometry

/-! The first-crossing barrier at the critical PWIT center. Small prefix
dimensions are excluded analytically, without finite tree enumeration. -/

@[expose] public section
namespace FreezingGrowth.PWIT

noncomputable def criticalCrossingBarrier (d j : ℕ) (a c : ℝ) : ℝ :=
  (j : ℝ) / d * timeCenter d - a - c * Real.log ((min j (d - j) : ℕ) + 1 : ℝ)

noncomputable def criticalCrossingOffset : ℝ := 30 * (5 / (2 * Real.exp 1)) + 1

theorem criticalCrossingOffset_pos : 0 < criticalCrossingOffset := by
  unfold criticalCrossingOffset
  positivity

theorem criticalCrossingBarrier_zero (d : ℕ) (a c : ℝ) :
    criticalCrossingBarrier d 0 a c = -a := by simp [criticalCrossingBarrier]

theorem criticalCrossingBarrier_self {d : ℕ} (hd : 0 < d) (a c : ℝ) :
    criticalCrossingBarrier d d a c = timeCenter d - a := by
  simp [criticalCrossingBarrier, Nat.cast_ne_zero.mpr hd.ne']

theorem criticalCrossingBarrier_small {d j : ℕ} (hd : 0 < d) (hj : j < 30)
    {a c : ℝ} (ha : criticalCrossingOffset ≤ a) (hc : 0 ≤ c) :
    criticalCrossingBarrier d j a c < 0 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have ht := mul_le_mul_of_nonneg_left (timeCenter_le_linear d)
    (div_nonneg (Nat.cast_nonneg (α := ℝ) j) hdR.le)
  have he : (j : ℝ) / d * (5 / (2 * Real.exp 1) * d) =
      (5 / (2 * Real.exp 1)) * j := by field_simp
  rw [he] at ht
  have hlog : 0 ≤ Real.log ((min j (d - j) : ℕ) + 1 : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ min j (d - j) + 1 by omega))
  have hjR : (j : ℝ) < 30 := by exact_mod_cast hj
  have hm := mul_le_mul_of_nonneg_left hjR.le
    (show (0 : ℝ) ≤ 5 / (2 * Real.exp 1) by positivity)
  unfold criticalCrossingBarrier
  unfold criticalCrossingOffset at ha
  nlinarith [mul_nonneg hc hlog]

theorem criticalCrossingBarrier_chord {d j i : ℕ} (hd : 0 < d) (hj : 0 < j) (a c : ℝ) :
    criticalCrossingBarrier d i a c - (i : ℝ) / j * criticalCrossingBarrier d j a c =
      -a + (i : ℝ) / j * a - c *
        (Real.log ((min i (d - i) : ℕ) + 1 : ℝ) -
          (i : ℝ) / j * Real.log ((min j (d - j) : ℕ) + 1 : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  unfold criticalCrossingBarrier
  field_simp
  ring

theorem criticalCrossingBarrier_first_half {d j i : ℕ} (hd : 0 < d) (hj : 0 < j)
    (hhalf : 2 * j ≤ d) (hij : i ≤ j) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    -a - c * Real.log ((min i (j - i) : ℕ) + 1 : ℝ) ≤
      criticalCrossingBarrier d i a c - (i : ℝ) / j * criticalCrossingBarrier d j a c := by
  rw [criticalCrossingBarrier_chord hd hj,
    Nat.min_eq_left (show i ≤ d - i by omega), Nat.min_eq_left (show j ≤ d - j by omega)]
  have hlog := mul_le_mul_of_nonneg_left (log_bridge_barrier_compare hj hij) hc
  have hapos := mul_nonneg (div_nonneg (Nat.cast_nonneg (α := ℝ) i)
    (Nat.cast_nonneg (α := ℝ) j)) ha
  linarith

theorem criticalCrossingBarrier_second_half {d j i : ℕ} (hd : 0 < d) (hj : 0 < j)
    (hjd : j ≤ d) (hij : i ≤ j) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    -(a + c * Real.log ((d - j : ℕ) + 1 : ℝ)) -
        c * Real.log ((min i (j - i) : ℕ) + 1 : ℝ) ≤
      criticalCrossingBarrier d i a c - (i : ℝ) / j * criticalCrossingBarrier d j a c := by
  rw [criticalCrossingBarrier_chord hd hj]
  have hlog := mul_le_mul_of_nonneg_left (log_min_window_bound hjd hij) hc
  have hLj : 0 ≤ Real.log ((min j (d - j) : ℕ) + 1 : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ min j (d - j) + 1 by omega))
  have hiR : 0 ≤ (i : ℝ) / j := div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg j)
  have hp := mul_nonneg hiR (mul_nonneg hc hLj)
  have hapos := mul_nonneg hiR ha
  nlinarith

end FreezingGrowth.PWIT
