module

public import FreezingGrowth.RRTGeometricRenewal
public import Mathlib.Algebra.Ring.GeomSum

/-! At each fixed height, the actual recursive-tree CDF decreases faster than
every fixed geometric sequence. The proof uses only the exact first-edge split
recurrence, with induction on height and then on the number of edges. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory

private theorem reflected_half_geometric_sum_le_two (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (n - k)) ≤ 2 := by
  have he : (∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (n - k)) =
      ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun k => (1 / 2 : ℝ) ^ k) (n + 1)
  rw [he]
  have hh := geom_sum_mul_neg (1 / 2 : ℝ) (n + 1)
  have hp : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  nlinarith

theorem heightCdfCoefficient_le_geometric (h : ℕ) :
    ∀ σ : ℝ, 0 < σ → ∃ D : ℝ, 0 ≤ D ∧
      ∀ n : ℕ, heightCdfCoefficient h n ≤ D * σ ^ n := by
  induction h with
  | zero =>
    intro σ hσ
    refine ⟨1, zero_le_one, ?_⟩
    intro n
    cases n with
    | zero => simp
    | succ n => rw [heightCdfCoefficient_zero_succ]; positivity
  | succ h ih =>
    intro σ hσ
    obtain ⟨C, hC₀, hC⟩ := ih (σ / 2) (by positivity)
    let N : ℕ := Nat.ceil (2 * C / σ) + 1
    have hNpos : 0 < N := by dsimp [N]; omega
    have hN : 2 * C / σ ≤ (N : ℝ) := by
      have hh := Nat.le_ceil (2 * C / σ)
      dsimp [N]
      push_cast
      linarith
    let D : ℝ := 1 + ∑ i ∈ Finset.range N, (σ ^ i)⁻¹
    have hD₀ : 0 ≤ D := by dsimp [D]; positivity
    have hsmall (n : ℕ) (hn : n < N) : heightCdfCoefficient (h + 1) n ≤ D * σ ^ n := by
      have hsingle : (σ ^ n)⁻¹ ≤ D := by
        have hh : (σ ^ n)⁻¹ ≤ ∑ i ∈ Finset.range N, (σ ^ i)⁻¹ :=
          Finset.single_le_sum (f := fun i : ℕ => (σ ^ i)⁻¹)
            (fun i _ => by positivity) (Finset.mem_range.mpr hn)
        dsimp [D]
        linarith
      have hh := mul_le_mul_of_nonneg_right hsingle (pow_nonneg hσ.le n)
      rw [inv_mul_cancel₀ (pow_ne_zero _ hσ.ne')] at hh
      exact (heightCdfCoefficient_le_one _ _).trans hh
    refine ⟨D, hD₀, ?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihsize =>
      by_cases hn : n < N
      · exact hsmall n hn
      · cases n with
        | zero => omega
        | succ n =>
          have hlarge : 2 * C ≤ ((n : ℝ) + 1) * σ := by
            have hh : (N : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : N ≤ n + 1)
            have hh' := (div_le_iff₀ hσ).mp hN
            nlinarith
          have hpoint (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
              heightCdfCoefficient (h + 1) k * heightCdfCoefficient h (n - k) ≤
                (D * C * σ ^ n) * (1 / 2 : ℝ) ^ (n - k) := by
            have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
            have hp : σ ^ k * σ ^ (n - k) = σ ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hk']
            calc
              _ ≤ (D * σ ^ k) * (C * (σ / 2) ^ (n - k)) :=
                mul_le_mul (ihsize k (Finset.mem_range.mp hk)) (hC (n - k))
                  (heightCdfCoefficient_nonneg h (n - k)) (by positivity)
              _ = D * C * (σ ^ k * σ ^ (n - k)) * (1 / 2 : ℝ) ^ (n - k) := by
                rw [show σ / 2 = σ * (1 / 2) by ring, mul_pow]
                ring
              _ = _ := by rw [hp]
          have hrec := RRTSplit.heightLaw_cdf_succ n h
          change heightCdfCoefficient (h + 1) (n + 1) =
            (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1),
              heightCdfCoefficient (h + 1) k * heightCdfCoefficient h (n - k) at hrec
          calc
            _ = (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1),
                heightCdfCoefficient (h + 1) k * heightCdfCoefficient h (n - k) := hrec
            _ ≤ (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1),
                (D * C * σ ^ n) * (1 / 2 : ℝ) ^ (n - k) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
            _ = (D * C * σ ^ n) / ((n : ℝ) + 1) *
                ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (n - k) := by
              rw [← Finset.mul_sum]
              ring
            _ ≤ (D * C * σ ^ n) / ((n : ℝ) + 1) * 2 :=
              mul_le_mul_of_nonneg_left (reflected_half_geometric_sum_le_two n) (by positivity)
            _ = (2 * C / ((n : ℝ) + 1)) * (D * σ ^ n) := by ring
            _ ≤ σ * (D * σ ^ n) :=
              mul_le_mul_of_nonneg_right
                ((div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
                  (by simpa only [mul_comm] using hlarge))
                (by positivity)
            _ = D * σ ^ (n + 1) := by rw [pow_succ]; ring

/-- The bound is for the actual RRT height law, for every edge count. -/
theorem heightLaw_boundedHeight_le_geometric (h : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      (Forward.heightLaw allAttach n).real {H | H ≤ h} ≤ D * σ ^ n :=
  heightCdfCoefficient_le_geometric h σ hσ

end FreezingGrowth.RRT
