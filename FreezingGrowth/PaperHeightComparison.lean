module

public import FreezingGrowth.PaperMeanThresholds
public import FreezingGrowth.RRTLowerTailPaperRate
public import FreezingGrowth.TwoSeedRemainders

/-! The source's polynomial comparison of independent recursive-tree heights.
The fixed lower-tail rate comes from seed amplification, rather than a sharp
mean-centered concentration theorem. The two source mean-event inclusions are
provided separately in `PaperMeanThresholds`. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory Filter
open scoped Topology

namespace TwoSeedCoupling

theorem comparisonLaw_threshold_union_bound (m n : ℕ) (T : ℝ) :
    (comparisonLaw m n).real {p | p.2 ≤ p.1} ≤
      (Forward.heightLaw RRT.allAttach m).real {h | T ≤ (h : ℝ)} +
      (Forward.heightLaw RRT.allAttach (n / 2)).real {h | (h : ℝ) ≤ T} := by
  let A : Set (ℕ × ℕ) := {h : ℕ | T ≤ (h : ℝ)} ×ˢ Set.univ
  let B : Set (ℕ × ℕ) := Set.univ ×ˢ {h : ℕ | (h : ℝ) ≤ T}
  have hsub : {p : ℕ × ℕ | p.2 ≤ p.1} ⊆ A ∪ B := by
    intro p hp
    by_cases hT : T ≤ (p.1 : ℝ)
    · exact Or.inl ⟨hT, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, by
        have hh : (p.2 : ℝ) ≤ p.1 := by exact_mod_cast hp
        change (p.2 : ℝ) ≤ T
        linarith⟩
  calc
    _ ≤ (comparisonLaw m n).real (A ∪ B) := measureReal_mono hsub
    _ ≤ (comparisonLaw m n).real A + (comparisonLaw m n).real B := measureReal_union_le _ _
    _ = _ := by simp [A, B, comparisonLaw, measureReal_prod_prod]

end TwoSeedCoupling

namespace RRT

theorem eventually_paper_tail_center_margins :
    ∀ᶠ n : ℕ in atTop,
      upperComparisonCenter (paperPrefixSize n) - Real.exp 1 / 2 * Real.log (n : ℝ) + 1 ≤
        -(1 / 8 : ℝ) * Real.log (n : ℝ) ∧
      Real.exp 1 / 2 * Real.log (n : ℝ) + 1 ≤
        lowerCenter 2 (n / 2) - 3 * Real.exp 1 / 8 * Real.log (n : ℝ) := by
  let C := 2 * Real.exp 1 * Real.log 2 + 1
  have he := Real.exp_one_gt_two
  have hsmall := (tendsto_order.mp (tendsto_rough_error_div_log C)).2
    (Real.exp 1 / 8) (by positivity)
  filter_upwards [eventually_ge_atTop 2, hsmall] with n hn hsmall
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have herr := (div_lt_iff₀ hlog).mp hsmall
  have hm := mul_le_mul_of_nonneg_left (paperPrefixSize_log_succ_le (by omega : 1 ≤ n))
    (Real.exp_pos 1).le
  have hh := mul_le_mul_of_nonneg_left (half_log_succ_ge (by omega : 1 ≤ n))
    (Real.exp_pos 1).le
  have hll := regularized_loglog_mono (Nat.div_le_self n 2)
  have hll0 : 0 ≤ Real.log (1 + Real.log ((n : ℝ) + 1)) := by
    apply Real.log_nonneg
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 1 by
      have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have htwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [upperComparisonCenter_eq]
  unfold lowerCenter
  dsimp [C] at herr
  constructor <;> nlinarith

theorem paper_small_height_tail :
    ∀ᶠ n : ℕ in atTop,
      (Forward.heightLaw allAttach (paperPrefixSize n)).real
        {h | Real.exp 1 / 2 * Real.log (n : ℝ) ≤ (h : ℝ)} ≤
          2 * Real.exp (-(1 / 8 : ℝ) * Real.log (n : ℝ)) := by
  filter_upwards [eventually_paper_tail_center_margins] with n hn
  have hsub : {h : ℕ | Real.exp 1 / 2 * Real.log (n : ℝ) ≤ (h : ℝ)} ⊆
      {h : ℕ | Real.exp 1 / 2 * Real.log (n : ℝ) - 1 < (h : ℝ)} := by
    intro h hh
    change Real.exp 1 / 2 * Real.log (n : ℝ) ≤ (h : ℝ) at hh
    change _ < _
    linarith
  apply (measureReal_mono hsub).trans
  apply (heightLaw_strict_upper_tail_exp (paperPrefixSize n)
    (Real.exp 1 / 2 * Real.log (n : ℝ) - 1)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact Real.exp_le_exp.mpr (by linarith [hn.1])

theorem paper_large_height_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (Forward.heightLaw allAttach (n / 2)).real
        {h | (h : ℝ) ≤ Real.exp 1 / 2 * Real.log (n : ℝ)} ≤
          C * Real.exp (-(1 / 8 : ℝ) * Real.log (n : ℝ)) := by
  obtain ⟨C, hC, htail⟩ := uniformLowerTailPaperRate
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_paper_tail_center_margins, eventually_ge_atTop 1] with n hn hn1
  let x := 3 * Real.exp 1 / 8 * Real.log (n : ℝ)
  have hx : 0 ≤ x := mul_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast hn1))
  have hsub : {h : ℕ | (h : ℝ) ≤ Real.exp 1 / 2 * Real.log (n : ℝ)} ⊆
      {h : ℕ | (h : ℝ) < Real.exp 1 / 2 * Real.log (n : ℝ) + 1} := by
    intro h hh
    change (h : ℝ) ≤ Real.exp 1 / 2 * Real.log (n : ℝ) at hh
    change _ < _
    linarith
  calc
    _ ≤ lowerTail (n / 2) (Real.exp 1 / 2 * Real.log (n : ℝ) + 1) := measureReal_mono hsub
    _ ≤ lowerTail (n / 2) (lowerCenter 2 (n / 2) - x) := lowerTail_mono _ hn.2
    _ ≤ C * Real.exp (-x / (3 * Real.exp 1)) := htail _ _ hx
    _ = _ := by
      congr 2
      dsimp [x]
      field_simp

end RRT

/-- Lemma 2.2(i), for the actual independent height laws and exact floor sizes.
The common constant with part (ii) must still be reconciled when proving (ii). -/
theorem paper_height_comparison_polynomial :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ n : ℕ in atTop,
      (TwoSeedCoupling.comparisonLaw (paperPrefixSize n) n).real {p | p.2 ≤ p.1} ≤
        2 * c₁ * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨C, hC, hlarge⟩ := RRT.paper_large_height_tail
  refine ⟨(2 + C) / 2, by positivity, ?_⟩
  filter_upwards [RRT.paper_small_height_tail, hlarge, eventually_ge_atTop 1] with n hs hl hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : Real.exp (-(1 / 8 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [Real.rpow_def_of_pos hnp]
    congr 1
    ring
  have hh := (TwoSeedCoupling.comparisonLaw_threshold_union_bound (paperPrefixSize n) n
    (Real.exp 1 / 2 * Real.log (n : ℝ))).trans (add_le_add hs hl)
  rw [hr] at hh
  nlinarith

end FreezingGrowth
