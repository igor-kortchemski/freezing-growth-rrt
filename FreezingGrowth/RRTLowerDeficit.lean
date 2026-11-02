module

public import FreezingGrowth.RRTLowerTailAmplification
public import FreezingGrowth.DeficitGrid

/-! Integrating the proved conditional lower tail on a finite grid. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory
open scoped Classical

def UniformLowerDeficit (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, lowerDeficit c n ≤ C

/-- The explicit deficit bound from a uniform seed. -/
theorem lowerDeficit_le_of_seed {c A p : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hp : 0 < p) (hp1 : p ≤ 1) (hseed : SeedAt c A p) (n : ℕ) :
    lowerDeficit c n ≤ A + (Real.exp 1 * Real.log 4) * (1 - p) /
      (1 - (1 - p / 2)) := by
  let L : ℝ := Real.exp 1 * Real.log 4
  let ρ : ℝ := 1 - p / 2
  have hL : 0 < L := mul_pos (Real.exp_pos 1) (Real.log_pos (by norm_num))
  have hρ : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (lowerCenter c n / L)
  have hb : lowerCenter c n ≤ (N : ℝ) * L :=
    (div_lt_iff₀ hL).mp hN |>.le
  let E (j : ℕ) : Set ℕ := {h | (h : ℝ) < lowerCenter c n - A - (j : ℝ) * L}
  let I (j : ℕ) : ℕ → ℝ := (E j).indicator (fun _ => 1)
  have hI (j : ℕ) : Integrable (I j) (Forward.heightLaw allAttach n) :=
    (integrable_const (1 : ℝ)).indicator (by measurability)
  have hpoint (h : ℕ) : max (lowerCenter c n - (h : ℝ)) 0 ≤
      A + L * ∑ j ∈ Finset.range N, I j h := by
    have hg := positivePart_le_grid hL.le N (lowerCenter c n - (h : ℝ) - A)
      (by have := Nat.cast_nonneg (α := ℝ) h; linarith)
    have he : (∑ j ∈ Finset.range N,
        (if (j : ℝ) * L < lowerCenter c n - (h : ℝ) - A then (1 : ℝ) else 0)) =
        ∑ j ∈ Finset.range N, I j h := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [I, E]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      have he : (j : ℝ) * L < lowerCenter c n - (h : ℝ) - A ↔
          (h : ℝ) < lowerCenter c n - A - (j : ℝ) * L := by constructor <;> intro hh <;> linarith
      simp only [he]
    rw [he] at hg
    apply max_le
    · have := le_max_left (lowerCenter c n - (h : ℝ) - A) 0
      linarith
    · have := le_max_right (lowerCenter c n - (h : ℝ) - A) 0
      linarith
  have hsum := integrable_finsetSum (Finset.range N) (fun j _ => hI j)
  calc
    lowerDeficit c n ≤ ∫ h : ℕ, (A + L * ∑ j ∈ Finset.range N, I j h)
        ∂Forward.heightLaw allAttach n :=
      integral_mono (lowerDeficit_integrable c n) ((integrable_const A).add (hsum.const_mul L)) hpoint
    _ = A + L * ∑ j ∈ Finset.range N, lowerTail n (lowerCenter c n - A - (j : ℝ) * L) := by
      rw [integral_add (integrable_const A) (hsum.const_mul L), integral_const,
        integral_const_mul, integral_finsetSum _ (fun j _ => hI j)]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_indicator_one (by measurability)
    _ ≤ A + L * ∑ j ∈ Finset.range N, (1 - p) * ρ ^ j := by
      gcongr with j hj
      exact lowerTail_geometric_of_seed hc hA hp hp1 hseed j n
    _ = A + L * (1 - p) * ∑ j ∈ Finset.range N, ρ ^ j := by rw [← Finset.mul_sum]; ring
    _ ≤ A + L * (1 - p) * (1 / (1 - ρ)) := by
      gcongr
      exact geom_sum_le_inv_one_sub hρ hρ1 N
    _ = _ := by dsimp [L, ρ]; ring

/-- The only unproved probabilistic input remains the seed itself. -/
theorem uniformLowerDeficit_of_seed {c : ℝ} (hc : 0 ≤ c) (hs : ConstantSuccessSeed c) :
    UniformLowerDeficit c := by
  obtain ⟨A, p, hA, hp, hp1, hseed⟩ := hs
  refine ⟨A + (Real.exp 1 * Real.log 4) * (1 - p) / (1 - (1 - p / 2)), ?_,
    lowerDeficit_le_of_seed hc hA hp hp1 hseed⟩
  have hL : 0 ≤ Real.exp 1 * Real.log 4 := by positivity
  exact add_nonneg hA (div_nonneg (mul_nonneg hL (by linarith)) (by linarith))

/-- The actual mean is bounded below by the center minus its positive deficit. -/
theorem lowerCenter_sub_deficit_le_mean (c : ℝ) (n : ℕ) :
    lowerCenter c n - lowerDeficit c n ≤ meanHeight n := by
  have hh := Forward.heightLaw_integrable allAttach n (fun h : ℕ => (h : ℝ))
  have hd := lowerDeficit_integrable c n
  have hi := integral_mono (integrable_const (lowerCenter c n)) (hh.add hd)
    (fun h : ℕ => (show lowerCenter c n ≤ (h : ℝ) +
      max (lowerCenter c n - (h : ℝ)) 0 by
        have := le_max_left (lowerCenter c n - (h : ℝ)) 0; linarith))
  simp only [Pi.add_apply] at hi
  rw [integral_add hh hd, integral_const, Forward.heightLaw_integral] at hi
  simp only [probReal_univ, smul_eq_mul, one_mul] at hi
  change lowerCenter c n ≤ meanHeight n + lowerDeficit c n at hi
  linarith

/-- Markov's bound at any real threshold below the center. -/
theorem gap_mul_lowerTail_le_deficit (c t : ℝ) (n : ℕ) :
    (lowerCenter c n - t) * lowerTail n t ≤ lowerDeficit c n := by
  let E : Set ℕ := {h | (h : ℝ) < t}
  have hpoint (h : ℕ) : E.indicator (fun _ => lowerCenter c n - t) h ≤
      max (lowerCenter c n - (h : ℝ)) 0 := by
    by_cases hh : h ∈ E
    · rw [Set.indicator_of_mem hh]
      have hh' : (h : ℝ) < t := hh
      have := le_max_left (lowerCenter c n - (h : ℝ)) 0
      linarith
    · rw [Set.indicator_of_notMem hh]
      exact le_max_right _ _
  have hi := integral_mono
    ((integrable_const (lowerCenter c n - t)).indicator (by measurability))
    (lowerDeficit_integrable c n) hpoint
  rw [integral_indicator_const _ (by measurability), smul_eq_mul, mul_comm] at hi
  exact hi

/-- An eventual seed is made uniform by enlarging its fixed offset; no finite
RRT probability calculations are needed. -/
theorem constantSuccessSeed_of_eventual {c A p : ℝ} (hc : 0 ≤ c)
    (hp : 0 < p) (hp1 : p ≤ 1) (N : ℕ)
    (hs : ∀ n : ℕ, N ≤ n → lowerTail n (lowerCenter c n - A) ≤ 1 - p) :
    ConstantSuccessSeed c := by
  let B : ℝ := Real.exp 1 * Real.log ((N : ℝ) + 1)
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos 1).le
    (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith))
  refine ⟨max A B, p, hB.trans (le_max_right _ _), hp, hp1, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (lowerTail_mono n (by have := le_max_left A B; linarith)).trans (hs n hn)
  · have hcenter : lowerCenter c n ≤ B := by
      have hln : 0 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hll : 0 ≤ Real.log (1 + Real.log ((n : ℝ) + 1)) :=
        Real.log_nonneg (by linarith)
      have hm := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
        (show (n : ℝ) + 1 ≤ (N : ℝ) + 1 by exact_mod_cast (by omega : n + 1 ≤ N + 1))
      have he := mul_le_mul_of_nonneg_left hm (Real.exp_pos 1).le
      dsimp [lowerCenter, B]
      nlinarith [mul_nonneg hc hll]
    have he : {h : ℕ | (h : ℝ) < lowerCenter c n - max A B} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro h hh
      have := le_max_right A B
      have := Nat.cast_nonneg (α := ℝ) h
      change (h : ℝ) < lowerCenter c n - max A B at hh
      linarith
    rw [lowerTail, he, measureReal_empty]
    linarith

end FreezingGrowth.RRT
