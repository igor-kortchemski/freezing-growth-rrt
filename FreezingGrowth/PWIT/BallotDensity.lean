module

public import FreezingGrowth.PWIT.TimeCenterEstimates

/-! Uniform density estimates for the polynomial near-leading bound.
This is calculus and factorial algebra; the near-leading probability estimate
is not an assumption-free conclusion of this file. -/

@[expose] public section
namespace FreezingGrowth.PWIT

theorem factorial_shift_six {n : ℕ} (hn : 12 ≤ n) :
    (n : ℝ) ^ 6 * ((n - 7).factorial : ℝ) ≤ 64 * ((n - 1).factorial : ℝ) := by
  have hh := Nat.factorial_mul_pow_le_factorial (m := n - 7) (n := 6)
  have he : n - 7 + 6 = n - 1 := by omega
  rw [he] at hh
  have hcast : ((n - 7).factorial : ℝ) * (((n - 7 : ℕ) : ℝ) + 1) ^ 6 ≤
      ((n - 1).factorial : ℝ) := by exact_mod_cast hh
  have hb : (n : ℝ) ≤ 2 * (((n - 7 : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega : 7 ≤ n)]
    norm_num
    have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) hb 6
  have hp' : (n : ℝ) ^ 6 ≤ 64 * (((n - 7 : ℕ) : ℝ) + 1) ^ 6 := by
    simpa only [mul_pow, show (2 : ℝ) ^ 6 = 64 by norm_num] using hp
  calc
    _ ≤ (64 * (((n - 7 : ℕ) : ℝ) + 1) ^ 6) * ((n - 7).factorial : ℝ) :=
      mul_le_mul_of_nonneg_right hp' (by positivity)
    _ = 64 * (((n - 7).factorial : ℝ) * (((n - 7 : ℕ) : ℝ) + 1) ^ 6) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcast (by norm_num)

theorem shifted_intensity_exp_upper {n m : ℕ} (hm : 0 < m)
    (hnm : (n : ℝ) ≤ 3 * (m : ℝ)) {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt n * (s ^ m / (m.factorial : ℝ)) ≤
      Real.sqrt 3 * Real.exp (Real.exp 1 * s - m) := by
  have hroot : Real.sqrt (n : ℝ) ≤ Real.sqrt 3 * Real.sqrt m := by
    calc
      _ ≤ Real.sqrt (3 * (m : ℝ)) := Real.sqrt_le_sqrt hnm
      _ = _ := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) (m : ℝ)
  calc
    _ ≤ (Real.sqrt 3 * Real.sqrt m) * (s ^ m / (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hroot (by positivity)
    _ = Real.sqrt 3 * (Real.sqrt m * (s ^ m / (m.factorial : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (generation_intensity_exp_upper hm hs) (Real.sqrt_nonneg _)

noncomputable def ballotPolynomial (n : ℕ) (A s : ℝ) : ℝ :=
  (1 / (n : ℝ)) * (s ^ (n - 1) / (n - 1).factorial +
    A ^ 6 * (n : ℝ) ^ 6 * s ^ (n - 7) / (n - 1).factorial)

theorem ballotPolynomial_eq {n : ℕ} (hn : 7 ≤ n) (A : ℝ) {s : ℝ} (hs : 0 < s) :
    ballotPolynomial n A s =
      (1 / (n : ℝ)) * (1 + (A * n / s) ^ 6) * (s ^ (n - 1) / (n - 1).factorial) := by
  have he : n - 1 = (n - 7) + 6 := by omega
  unfold ballotPolynomial
  rw [he, pow_add]
  field_simp

noncomputable def ballotDensityConstant : ℝ := 64 * Real.sqrt 3 * Real.exp 7

theorem ballotDensityConstant_pos : 0 < ballotDensityConstant := by
  unfold ballotDensityConstant
  positivity

theorem ballotPolynomial_exp_upper {n : ℕ} (hn : 12 ≤ n) {A s : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) :
    ballotPolynomial n A s ≤ ballotDensityConstant * (1 + A ^ 6) /
      ((n : ℝ) * Real.sqrt n) * Real.exp (Real.exp 1 * s - n) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hm1 : 0 < n - 1 := by omega
  have hm7 : 0 < n - 7 := by omega
  have hnm1 : (n : ℝ) ≤ 3 * ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnm7 : (n : ℝ) ≤ 3 * ((n - 7 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 7 ≤ n)]
    norm_num
    have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 := shifted_intensity_exp_upper hm1 hnm1 hs
  have h7 := shifted_intensity_exp_upper hm7 hnm7 hs
  have hexp : Real.exp (Real.exp 1 * s - ((n - 1 : ℕ) : ℝ)) ≤
      Real.exp (Real.exp 1 * s - ((n - 7 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh : ((n - 7 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n - 7 ≤ n - 1)
    linarith
  have h1' : Real.sqrt n * (s ^ (n - 1) / ((n - 1).factorial : ℝ)) ≤
      Real.sqrt 3 * Real.exp (Real.exp 1 * s - ((n - 7 : ℕ) : ℝ)) :=
    h1.trans (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _))
  have hratio : (n : ℝ) ^ 6 * s ^ (n - 7) / ((n - 1).factorial : ℝ) ≤
      64 * (s ^ (n - 7) / ((n - 7).factorial : ℝ)) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n - 1).factorial)).mpr
    have hh := mul_le_mul_of_nonneg_right (factorial_shift_six hn)
      (div_nonneg (pow_nonneg hs (n - 7)) (by positivity : (0 : ℝ) ≤ (n - 7).factorial))
    convert hh using 1
    · field_simp
    · ring
  have hterm : Real.sqrt n *
      (A ^ 6 * (n : ℝ) ^ 6 * s ^ (n - 7) / ((n - 1).factorial : ℝ)) ≤
      (64 * A ^ 6) * (Real.sqrt 3 * Real.exp (Real.exp 1 * s - ((n - 7 : ℕ) : ℝ))) := by
    have hh := (mul_le_mul_of_nonneg_left hratio (pow_nonneg hA 6))
    have hh' := mul_le_mul_of_nonneg_left hh hsqrt.le
    calc
      _ ≤ Real.sqrt n * (A ^ 6 * (64 * (s ^ (n - 7) / ((n - 7).factorial : ℝ)))) := by
        convert hh' using 1; ring
      _ = (64 * A ^ 6) * (Real.sqrt n * (s ^ (n - 7) / ((n - 7).factorial : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h7 (by positivity)
  have htotal := add_le_add h1' hterm
  have he : Real.exp (Real.exp 1 * s - ((n - 7 : ℕ) : ℝ)) =
      Real.exp 7 * Real.exp (Real.exp 1 * s - n) := by
    rw [← Real.exp_add, Nat.cast_sub (by omega : 7 ≤ n)]
    congr 1
    norm_num
    ring
  rw [he] at htotal
  unfold ballotPolynomial ballotDensityConstant
  simp only [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hnpos hsqrt)).mpr
  have hcoeff : (1 : ℝ) + 64 * A ^ 6 ≤ 64 * (1 + A ^ 6) := by linarith
  have hb := mul_le_mul_of_nonneg_right hcoeff
    (by positivity : 0 ≤ Real.sqrt 3 * (Real.exp 7 * Real.exp (Real.exp 1 * s - n)))
  have hmain := htotal.trans (by convert hb using 1; ring)
  convert hmain using 1
  · field_simp
  · ring

end FreezingGrowth.PWIT
