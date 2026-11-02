module

public import FreezingGrowth.RRTNegativeMoment

/-! Strong induction for the negative height moment. -/

@[expose] public section
namespace FreezingGrowth.RRT

open Filter
open scoped Topology

theorem sum_half_reciprocals (n : ℕ) :
    (∑ j ∈ Finset.Ico (n / 2) n, (1 : ℝ) / (j + 1)) =
      (harmonic n : ℝ) - (harmonic (n / 2) : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ (Nat.div_le_self n 2)]
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem negativeMoment_bound : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    negativeMoment n ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_half_harmonic_contraction
  let C : ℝ := (N : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · apply (negativeMoment_le_one n).trans
      apply (le_div_iff₀ (by positivity)).mpr
      dsimp [C]
      rw [one_mul]
      exact_mod_cast (show n + 1 ≤ N + 1 by omega)
    · have hn0 : 0 < n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hrec : (n : ℝ) * negativeMoment n ≤
          (10 / 7 : ℝ) * ∑ j ∈ Finset.Ico (n / 2) n, negativeMoment j := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
        simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using negativeMoment_succ_le m
      have hsum : (∑ j ∈ Finset.Ico (n / 2) n, negativeMoment j) ≤
          C * ((harmonic n : ℝ) - (harmonic (n / 2) : ℝ)) := by
        calc
          _ ≤ ∑ j ∈ Finset.Ico (n / 2) n, C / ((j : ℝ) + 1) :=
            Finset.sum_le_sum (fun j hj => ih j (Finset.mem_Ico.mp hj).2)
          _ = C * ∑ j ∈ Finset.Ico (n / 2) n, (1 : ℝ) / ((j : ℝ) + 1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = _ := by rw [sum_half_reciprocals]
      have hcoef := hN n (by omega)
      have hnr0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
      have hnr1 : (n : ℝ) + 1 ≠ 0 := by positivity
      calc
        negativeMoment n ≤
            ((10 / 7 : ℝ) * C * ((harmonic n : ℝ) - (harmonic (n / 2) : ℝ))) / n := by
          apply (le_div_iff₀ hnR).mpr
          nlinarith
        _ = (C / ((n : ℝ) + 1)) *
            ((10 / 7 : ℝ) * ((n : ℝ) + 1) / n *
              ((harmonic n : ℝ) - (harmonic (n / 2) : ℝ))) := by
          field_simp
        _ ≤ C / ((n : ℝ) + 1) * 1 :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = C / ((n : ℝ) + 1) := mul_one _

end FreezingGrowth.RRT
