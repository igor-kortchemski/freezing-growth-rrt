module

public import FreezingGrowth.PWIT.BallotDensity

/-! Factorial-shift intensity estimates for any fixed polynomial degree.
The threshold is explicit and includes degrees zero and one. -/

@[expose] public section
namespace FreezingGrowth.PWIT

theorem factorial_shift_degree (P : ℕ) {n : ℕ} (hn : 2 * (P + 1) ≤ n) :
    (n : ℝ) ^ P * ((n - (P + 1)).factorial : ℝ) ≤
      (2 : ℝ) ^ P * ((n - 1).factorial : ℝ) := by
  have hh := Nat.factorial_mul_pow_le_factorial (m := n - (P + 1)) (n := P)
  have he : n - (P + 1) + P = n - 1 := by omega
  rw [he] at hh
  have hcast : ((n - (P + 1)).factorial : ℝ) * (((n - (P + 1) : ℕ) : ℝ) + 1) ^ P ≤
      ((n - 1).factorial : ℝ) := by exact_mod_cast hh
  have hnR : 2 * ((P : ℝ) + 1) ≤ n := by exact_mod_cast hn
  have hb : (n : ℝ) ≤ 2 * (((n - (P + 1) : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega : P + 1 ≤ n), Nat.cast_add, Nat.cast_one]
    linarith
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) hb P
  rw [mul_pow] at hp
  calc
    _ ≤ ((2 : ℝ) ^ P * (((n - (P + 1) : ℕ) : ℝ) + 1) ^ P) *
        ((n - (P + 1)).factorial : ℝ) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (2 : ℝ) ^ P * (((n - (P + 1)).factorial : ℝ) *
        (((n - (P + 1) : ℕ) : ℝ) + 1) ^ P) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcast (by positivity)

theorem shifted_intensity_exp_upper_half {n m : ℕ} (hm : 0 < m)
    (hnm : (n : ℝ) ≤ 2 * (m : ℝ)) {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt n * (s ^ m / (m.factorial : ℝ)) ≤
      Real.sqrt 2 * Real.exp (Real.exp 1 * s - m) := by
  have hroot : Real.sqrt (n : ℝ) ≤ Real.sqrt 2 * Real.sqrt m := by
    calc
      _ ≤ Real.sqrt (2 * (m : ℝ)) := Real.sqrt_le_sqrt hnm
      _ = _ := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (m : ℝ)
  calc
    _ ≤ (Real.sqrt 2 * Real.sqrt m) * (s ^ m / (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hroot (by positivity)
    _ = Real.sqrt 2 * (Real.sqrt m * (s ^ m / (m.factorial : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (generation_intensity_exp_upper hm hs) (Real.sqrt_nonneg _)

noncomputable def degreeBallotPolynomial (P n : ℕ) (A s : ℝ) : ℝ :=
  (1 / (n : ℝ)) * (s ^ (n - 1) / (n - 1).factorial +
    A ^ P * (n : ℝ) ^ P * s ^ (n - (P + 1)) / (n - 1).factorial)

theorem degreeBallotPolynomial_eq (P : ℕ) {n : ℕ} (hn : P + 1 ≤ n)
    (A : ℝ) {s : ℝ} (hs : 0 < s) :
    degreeBallotPolynomial P n A s =
      (1 / (n : ℝ)) * (1 + (A * n / s) ^ P) *
        (s ^ (n - 1) / (n - 1).factorial) := by
  have he : n - 1 = (n - (P + 1)) + P := by omega
  unfold degreeBallotPolynomial
  rw [he, pow_add, div_pow, mul_pow]
  field_simp [pow_ne_zero P hs.ne']

noncomputable def degreeBallotDensityConstant (P : ℕ) : ℝ :=
  (2 : ℝ) ^ P * Real.sqrt 2 * Real.exp ((P : ℝ) + 1)

theorem degreeBallotDensityConstant_pos (P : ℕ) : 0 < degreeBallotDensityConstant P := by
  unfold degreeBallotDensityConstant
  positivity

theorem degreeBallotPolynomial_exp_upper (P : ℕ) {n : ℕ} (hn : 2 * (P + 1) ≤ n)
    {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    degreeBallotPolynomial P n A s ≤ degreeBallotDensityConstant P * (1 + A ^ P) /
      ((n : ℝ) * Real.sqrt n) * Real.exp (Real.exp 1 * s - n) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hm1 : 0 < n - 1 := by omega
  have hmP : 0 < n - (P + 1) := by omega
  have hnR : 2 * ((P : ℝ) + 1) ≤ n := by exact_mod_cast hn
  have hnm1 : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    linarith
  have hnmP : (n : ℝ) ≤ 2 * ((n - (P + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : P + 1 ≤ n), Nat.cast_add, Nat.cast_one]
    linarith
  have h1 := shifted_intensity_exp_upper_half hm1 hnm1 hs
  have hP := shifted_intensity_exp_upper_half hmP hnmP hs
  have hexp : Real.exp (Real.exp 1 * s - ((n - 1 : ℕ) : ℝ)) ≤
      Real.exp (Real.exp 1 * s - ((n - (P + 1) : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh : ((n - (P + 1) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (by omega)
    linarith
  have h1' : Real.sqrt n * (s ^ (n - 1) / ((n - 1).factorial : ℝ)) ≤
      Real.sqrt 2 * Real.exp (Real.exp 1 * s - ((n - (P + 1) : ℕ) : ℝ)) :=
    h1.trans (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _))
  have hratio : (n : ℝ) ^ P * s ^ (n - (P + 1)) / ((n - 1).factorial : ℝ) ≤
      (2 : ℝ) ^ P * (s ^ (n - (P + 1)) / ((n - (P + 1)).factorial : ℝ)) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n - 1).factorial)).mpr
    have hh := mul_le_mul_of_nonneg_right (factorial_shift_degree P hn)
      (div_nonneg (pow_nonneg hs (n - (P + 1)))
        (by positivity : (0 : ℝ) ≤ (n - (P + 1)).factorial))
    convert hh using 1
    · field_simp
    · ring
  have hterm : Real.sqrt n *
      (A ^ P * (n : ℝ) ^ P * s ^ (n - (P + 1)) / ((n - 1).factorial : ℝ)) ≤
      ((2 : ℝ) ^ P * A ^ P) *
        (Real.sqrt 2 * Real.exp (Real.exp 1 * s - ((n - (P + 1) : ℕ) : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_left hratio (pow_nonneg hA P)
    have hh' := mul_le_mul_of_nonneg_left hh hsqrt.le
    calc
      _ ≤ Real.sqrt n * (A ^ P * ((2 : ℝ) ^ P *
          (s ^ (n - (P + 1)) / ((n - (P + 1)).factorial : ℝ)))) := by
        convert hh' using 1; ring
      _ = ((2 : ℝ) ^ P * A ^ P) *
          (Real.sqrt n * (s ^ (n - (P + 1)) / ((n - (P + 1)).factorial : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
  have htotal := add_le_add h1' hterm
  have he : Real.exp (Real.exp 1 * s - ((n - (P + 1) : ℕ) : ℝ)) =
      Real.exp ((P : ℝ) + 1) * Real.exp (Real.exp 1 * s - n) := by
    rw [← Real.exp_add, Nat.cast_sub (by omega : P + 1 ≤ n), Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  rw [he] at htotal
  unfold degreeBallotPolynomial degreeBallotDensityConstant
  simp only [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hnpos hsqrt)).mpr
  have htwo : (1 : ℝ) ≤ 2 ^ P := one_le_pow₀ (by norm_num)
  have hcoeff : 1 + (2 : ℝ) ^ P * A ^ P ≤ (2 : ℝ) ^ P * (1 + A ^ P) := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hcoeff
    (by positivity : 0 ≤ Real.sqrt 2 *
      (Real.exp ((P : ℝ) + 1) * Real.exp (Real.exp 1 * s - n)))
  have hmain := htotal.trans (by convert hb using 1; ring)
  convert hmain using 1
  · field_simp
  · ring

end FreezingGrowth.PWIT
