module

public import FreezingGrowth.RRTCriticalUpperTransfer

/-! Conditional critical-center absolute-deviation bounds. The upper clock
estimate is an explicit premise throughout; the lower estimate is already
proved for the actual recursive-tree laws. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory
open scoped Classical

noncomputable def polynomialExpAbsorptionConstant (P : ℕ) : ℝ :=
  (2 : ℝ) ^ P * P.factorial * Real.exp (1 / 2)

theorem polynomialExpAbsorptionConstant_pos (P : ℕ) :
    0 < polynomialExpAbsorptionConstant P := by
  unfold polynomialExpAbsorptionConstant
  positivity

theorem polynomial_exp_absorption (P : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ P * Real.exp (-x) ≤
      polynomialExpAbsorptionConstant P * Real.exp (-x / 2) := by
  have hh := Real.pow_div_factorial_le_exp ((1 + x) / 2) (show 0 ≤ (1 + x) / 2 by linarith) P
  have hp := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ ((2 : ℝ) ^ P * P.factorial) * Real.exp (-x) by positivity)
  have hleft : ((1 + x) / 2) ^ P / P.factorial *
      (((2 : ℝ) ^ P * P.factorial) * Real.exp (-x)) = (1 + x) ^ P * Real.exp (-x) := by
    rw [div_pow]
    field_simp
  have hright : Real.exp ((1 + x) / 2) *
      (((2 : ℝ) ^ P * P.factorial) * Real.exp (-x)) =
        polynomialExpAbsorptionConstant P * Real.exp (-x / 2) := by
    have he : Real.exp ((1 + x) / 2) * Real.exp (-x) =
        Real.exp (1 / 2) * Real.exp (-x / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    unfold polynomialExpAbsorptionConstant
    calc
      _ = ((2 : ℝ) ^ P * P.factorial) *
          (Real.exp ((1 + x) / 2) * Real.exp (-x)) := by ring
      _ = ((2 : ℝ) ^ P * P.factorial) *
          (Real.exp (1 / 2) * Real.exp (-x / 2)) := by rw [he]
      _ = _ := by ring
  rwa [hleft, hright] at hp

/-- Integrating a uniform exponential tail on the actual finite height law. -/
theorem upperExcessAt_le_of_half_exp_tail (n : ℕ) {a D : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D)
    (htail : ∀ x : ℝ, 0 ≤ x →
      (Forward.heightLaw allAttach n).real {h | a + x < (h : ℝ)} ≤ D * Real.exp (-x / 2)) :
    upperExcessAt n a ≤ D / (1 - Real.exp (-(1 / 2))) := by
  let E (j : ℕ) : Set ℕ := {h | a + (j : ℝ) < (h : ℝ)}
  let I (j : ℕ) : ℕ → ℝ := (E j).indicator (fun _ => 1)
  let ρ : ℝ := Real.exp (-(1 / 2))
  have hI (j : ℕ) : Integrable (I j) (Forward.heightLaw allAttach n) :=
    (integrable_const 1).indicator (by measurability)
  have hsum := integrable_finsetSum (Finset.range n) (fun j _ => hI j)
  have hpoint : ∀ᵐ h : ℕ ∂Forward.heightLaw allAttach n,
      max ((h : ℝ) - a) 0 ≤ ∑ j ∈ Finset.range n, I j h := by
    filter_upwards [heightLaw_ae_le_edges n] with h hh
    have hh' : (h : ℝ) ≤ n := by exact_mod_cast hh
    have hg := positivePart_le_grid (L := 1) (by norm_num) n ((h : ℝ) - a) (by linarith)
    simp only [one_mul, mul_one] at hg
    have he : (∑ j ∈ Finset.range n, if (j : ℝ) < (h : ℝ) - a then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range n, I j h := by
      apply Finset.sum_congr rfl
      intro j _
      change (if (j : ℝ) < (h : ℝ) - a then (1 : ℝ) else 0) = (E j).indicator (fun _ => 1) h
      by_cases hj : (j : ℝ) < (h : ℝ) - a
      · have hm : h ∈ E j := by change a + (j : ℝ) < h; linarith
        rw [ite_eq_left hj, Set.indicator_of_mem hm]
      · have hm : h ∉ E j := by change ¬(a + (j : ℝ) < (h : ℝ)); linarith
        rw [ite_eq_right hj, Set.indicator_of_notMem hm]
    rwa [he] at hg
  have ht (j : ℕ) : (Forward.heightLaw allAttach n).real (E j) ≤ D * ρ ^ j := by
    have hh := htail j (Nat.cast_nonneg j)
    have he : Real.exp (-(j : ℝ) / 2) = ρ ^ j := by
      dsimp [ρ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rwa [he] at hh
  have hρ : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  calc
    upperExcessAt n a ≤ ∫ h : ℕ, ∑ j ∈ Finset.range n, I j h ∂Forward.heightLaw allAttach n :=
      integral_mono_ae (upperExcessAt_integrable n a) hsum hpoint
    _ = ∑ j ∈ Finset.range n, (Forward.heightLaw allAttach n).real (E j) := by
      rw [integral_finsetSum _ (fun j _ => hI j)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_indicator_one (by measurability)
    _ ≤ ∑ j ∈ Finset.range n, D * ρ ^ j := Finset.sum_le_sum (fun j _ => ht j)
    _ = D * ∑ j ∈ Finset.range n, ρ ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ D * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hρ hρ1 n) hD
    _ = _ := by dsimp [ρ]; ring

theorem upperExcessAt_le_add_shift (n : ℕ) (b : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    upperExcessAt n b ≤ A + upperExcessAt n (b + A) := by
  have hpoint (h : ℕ) : max ((h : ℝ) - b) 0 ≤ A + max ((h : ℝ) - (b + A)) 0 := by
    apply max_le
    · have := le_max_left ((h : ℝ) - (b + A)) 0
      linarith
    · have := le_max_right ((h : ℝ) - (b + A)) 0
      linarith
  have hh := integral_mono (upperExcessAt_integrable n b)
    ((integrable_const A).add (upperExcessAt_integrable n (b + A))) hpoint
  have hsum := integral_add (integrable_const A) (upperExcessAt_integrable n (b + A))
  dsimp only [Pi.add_apply] at hh
  rw [hsum, integral_const] at hh
  simpa only [probReal_univ, smul_eq_mul, one_mul, upperExcessAt] using hh

theorem uniformCriticalUpperExcess_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, upperExcessAt n (lowerCenter (3 / 2) n) ≤ B := by
  have hC : 0 ≤ C := by
    have hh := hclock d₀ le_rfl 0 le_rfl
    simp only [add_zero, one_pow, neg_zero, Real.exp_zero, mul_one] at hh
    exact measureReal_nonneg.trans hh
  obtain ⟨A, hA, htail⟩ := heightLaw_critical_upper_tail_of_clock hclock
  let D := 2 * C * polynomialExpAbsorptionConstant P
  have hD : 0 ≤ D := mul_nonneg (by linarith) (polynomialExpAbsorptionConstant_pos P).le
  have hρ : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨A + D / (1 - Real.exp (-(1 / 2))), by positivity, ?_⟩
  intro n
  apply (upperExcessAt_le_add_shift n (lowerCenter (3 / 2) n) hA).trans
  apply add_le_add le_rfl
  have hanchor : 0 ≤ lowerCenter (3 / 2) n + A := by
    have hl : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    exact add_nonneg (hl.trans (lowerCenter_critical_ge_log n)) hA
  apply upperExcessAt_le_of_half_exp_tail n hanchor hD
  intro x hx
  have hsub : {h : ℕ | lowerCenter (3 / 2) n + A + x < (h : ℝ)} ⊆
      {h : ℕ | lowerCenter (3 / 2) n + A + x ≤ (h : ℝ)} := by
    intro h hh
    change lowerCenter (3 / 2) n + A + x ≤ (h : ℝ)
    exact (show lowerCenter (3 / 2) n + A + x < (h : ℝ) from hh).le
  apply (measureReal_mono hsub).trans ((htail n x hx).trans _)
  have hh := mul_le_mul_of_nonneg_left (polynomial_exp_absorption P hx)
    (show 0 ≤ 2 * C by linarith)
  simpa only [D, mul_assoc] using hh

noncomputable def criticalAbsoluteDeviation (n : ℕ) : ℝ :=
  ∫ h : ℕ, |(h : ℝ) - lowerCenter (3 / 2) n| ∂Forward.heightLaw allAttach n

theorem criticalAbsoluteDeviation_integrable (n : ℕ) :
    Integrable (fun h : ℕ => |(h : ℝ) - lowerCenter (3 / 2) n|) (Forward.heightLaw allAttach n) :=
  Forward.heightLaw_integrable allAttach n _

theorem criticalAbsoluteDeviation_nonneg (n : ℕ) : 0 ≤ criticalAbsoluteDeviation n :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem criticalAbsoluteDeviation_le_excess_add_deficit (n : ℕ) :
    criticalAbsoluteDeviation n ≤ upperExcessAt n (lowerCenter (3 / 2) n) + lowerDeficit (3 / 2) n := by
  let b := lowerCenter (3 / 2) n
  have hpoint (h : ℕ) : |(h : ℝ) - b| ≤ max ((h : ℝ) - b) 0 + max (b - (h : ℝ)) 0 := by
    have hu := le_max_left ((h : ℝ) - b) 0
    have hu0 := le_max_right ((h : ℝ) - b) 0
    have hl := le_max_left (b - (h : ℝ)) 0
    have hl0 := le_max_right (b - (h : ℝ)) 0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hu := upperExcessAt_integrable n b
  have hl := lowerDeficit_integrable (3 / 2) n
  have hh := integral_mono (criticalAbsoluteDeviation_integrable n) (hu.add hl) hpoint
  have hsum := integral_add hu hl
  dsimp only [Pi.add_apply] at hh
  rw [hsum] at hh
  exact hh

/-- The actual upper clock estimate is the only remaining premise in this
uniform critical-center absolute-deviation bound. -/
theorem uniformCriticalAbsoluteDeviation_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, criticalAbsoluteDeviation n ≤ B := by
  obtain ⟨U, hU, hupper⟩ := uniformCriticalUpperExcess_of_clock hclock
  obtain ⟨D, hD, hlower⟩ := uniformLowerDeficit_critical
  exact ⟨U + D, add_nonneg hU hD, fun n =>
    (criticalAbsoluteDeviation_le_excess_add_deficit n).trans (add_le_add (hupper n) (hlower n))⟩

theorem meanHeight_critical_deviation_le (n : ℕ) :
    |meanHeight n - lowerCenter (3 / 2) n| ≤ criticalAbsoluteDeviation n := by
  have hh := norm_integral_le_integral_norm (μ := Forward.heightLaw allAttach n)
    (f := fun h : ℕ => (h : ℝ) - lowerCenter (3 / 2) n)
  have hsub := integral_sub (Forward.heightLaw_integrable allAttach n (fun h : ℕ => (h : ℝ)))
    (integrable_const (lowerCenter (3 / 2) n))
  rw [hsub, integral_const, Forward.heightLaw_integral] at hh
  simpa only [Real.norm_eq_abs, probReal_univ, smul_eq_mul, one_mul, meanHeight,
    criticalAbsoluteDeviation] using hh

theorem uniformCriticalMeanDeviation_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |meanHeight n - lowerCenter (3 / 2) n| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := uniformCriticalAbsoluteDeviation_of_clock hclock
  exact ⟨B, hB, fun n => (meanHeight_critical_deviation_le n).trans (hbound n)⟩

end FreezingGrowth.RRT
