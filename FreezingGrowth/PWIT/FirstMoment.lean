module

public import FreezingGrowth.PWIT.Erlang
public import FreezingGrowth.PWIT.RankCounts

/-! # Finite rank-class birth counts and their actual expectations -/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def rankBirthCount (d k : ℕ) (t : ℝ) (ω : Sample) : ℝ :=
  ∑ v ∈ rankClass d k, {ω | birth ω v ≤ t}.indicator (fun _ => (1 : ℝ)) ω

theorem integrable_rankBirthCount (d k : ℕ) (t : ℝ) :
    Integrable (rankBirthCount d k t) law := by
  unfold rankBirthCount
  exact integrable_finsetSum _ fun v _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_le (measurable_birth v) measurable_const)

theorem integral_rankBirthCount {d : ℕ} (hd : 0 < d) (k : ℕ) (t : ℝ) :
    (∫ ω, rankBirthCount d k t ω ∂law) =
      (rankClass d k).card * (gammaMeasure ((d : ℝ) + k) 1).real (Set.Iic t) := by
  classical
  unfold rankBirthCount
  rw [integral_finsetSum]
  · calc
      _ = ∑ _v ∈ rankClass d k, (gammaMeasure ((d : ℝ) + k) 1).real (Set.Iic t) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [integral_indicator_const (μ := law) (1 : ℝ)
          (measurableSet_le (measurable_birth v) measurable_const), smul_eq_mul, mul_one]
        have hvlen := (mem_rankClass.mp hv).1
        have hvne : v ≠ [] := by intro he; simp [he] at hvlen; omega
        have hs := (mem_rankClass_iff_rankSum.mp hv).2
        have hm := map_birth_gamma hvne
        have he : law.real {ω | birth ω v ≤ t} =
            (law.map (fun ω => birth ω v)).real (Set.Iic t) := by
          rw [measureReal_def, measureReal_def,
            Measure.map_apply (measurable_birth v) measurableSet_Iic]
          rfl
        rw [he, hm, hs]
        congr 2
        push_cast
        rfl
      _ = _ := by simp [nsmul_eq_mul]
  · intro v _
    exact (integrable_const (1 : ℝ)).indicator
      (measurableSet_le (measurable_birth v) measurable_const)

/-- The exact finite-slice first moment, in the notation of AF13 Section 3. -/
theorem integral_rankBirthCount_eq_choose {d : ℕ} (hd : 0 < d) (k : ℕ) (t : ℝ) :
    (∫ ω, rankBirthCount d k t ω ∂law) =
      ((d + k - 1).choose k : ℝ) *
        (gammaMeasure ((d : ℝ) + k) 1).real (Set.Iic t) := by
  rw [integral_rankBirthCount hd, card_rankClass_choose hd]

/-- The density factorization used for the rank window in AF13 Section 3.
Here the generation is `d + 1` and the excess rank is `k`. -/
theorem rank_density_factor (d k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((d + k).choose k : ℝ) * gammaPDFReal (((d + k : ℕ) : ℝ) + 1) 1 x =
      (x ^ k / k.factorial) * (x ^ d * Real.exp (-x) / d.factorial) := by
  have hf : ((d + k).choose k : ℝ) * (d.factorial : ℝ) * k.factorial =
      ((d + k).factorial : ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial d k
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hdk : ((d + k).factorial : ℝ) ≠ 0 := by positivity
  simp only [gammaPDFReal, ite_eq_left hx, Real.one_rpow, Real.Gamma_nat_eq_factorial,
    add_sub_cancel_right, Real.rpow_natCast, one_mul, pow_add]
  field_simp
  linear_combination (x ^ d * x ^ k) * hf

end FreezingGrowth.PWIT
