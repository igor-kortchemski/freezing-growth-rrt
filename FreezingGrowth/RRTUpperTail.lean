module

public import FreezingGrowth.PWIT.HeightBridge
public import FreezingGrowth.PWIT.GenerationCount
public import FreezingGrowth.PWIT.TimeCenterEstimates
public import FreezingGrowth.DeficitGrid
public import FreezingGrowth.LowProfile
public import FreezingGrowth.TreeCounts
import Mathlib.Algebra.Order.Ring.Pow

/-!
# A coarse uniform upper tail for actual recursive-tree heights

The geometric mixture and the actual PWIT first moment give an exponential
upper tail. This does not assert the sharper height results E1 or E2.
-/

@[expose] public section

namespace FreezingGrowth.RRT

open MeasureTheory
open scoped ENNReal NNReal Classical

theorem geometricIndexLaw_tail_ge (t : ℝ≥0) (n : ℕ) :
    (geometricIndexLaw t).real {k | n ≤ k} = (1 - Real.exp (-(t : ℝ))) ^ n := by
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.succ_le_iff] using geometricIndexLaw_tail t n

/-- Larger deterministic trees contribute at least their smaller-tree tail to
the geometric mixture. No independence between height and index is used. -/
theorem geometricHeightLaw_tail_ge (t : ℝ≥0) (n d : ℕ) :
    (Forward.heightLaw allAttach n).real {h | d ≤ h} *
      (geometricIndexLaw t).real {k | n ≤ k} ≤
        (geometricHeightLaw t).real {h | d ≤ h} := by
  let a := (Forward.heightLaw allAttach n).real {h | d ≤ h}
  have hI : Integrable ({k : ℕ | n ≤ k}.indicator (fun _ => a)) (geometricIndexLaw t) :=
    (integrable_const a).indicator (Set.to_countable _).measurableSet
  have hpoint (k : ℕ) : {k : ℕ | n ≤ k}.indicator (fun _ => a) k ≤
      (Forward.heightLaw allAttach k).real {h | d ≤ h} := by
    by_cases hk : n ≤ k
    · rw [Set.indicator_of_mem (show k ∈ {k : ℕ | n ≤ k} from hk)]
      exact Forward.heightLaw_real_tail_mono_time allAttach hk d
    · rw [Set.indicator_of_notMem (show k ∉ {k : ℕ | n ≤ k} from hk)]
      exact measureReal_nonneg
  rw [geometricHeightLaw_real_eq_integral]
  have hi := integral_mono hI (geometricHeightLaw_event_integrable t {h | d ≤ h}) hpoint
  rw [integral_indicator_const a (Set.to_countable _).measurableSet, smul_eq_mul] at hi
  simpa only [a, mul_comm] using hi

noncomputable def upperComparisonTime (n : ℕ) : ℝ≥0 :=
  ⟨Real.log (2 * ((n : ℝ) + 1)), Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith)⟩

theorem upperComparisonTime_exp_neg (n : ℕ) :
    Real.exp (-(upperComparisonTime n : ℝ)) = 1 / (2 * ((n : ℝ) + 1)) := by
  change Real.exp (-Real.log (2 * ((n : ℝ) + 1))) = _
  rw [Real.exp_neg, Real.exp_log (by positivity), one_div]

theorem upperComparisonTime_index_tail (n : ℕ) :
    (1 / 2 : ℝ) ≤ (geometricIndexLaw (upperComparisonTime n)).real {k | n ≤ k} := by
  rw [geometricIndexLaw_tail_ge, upperComparisonTime_exp_neg]
  let p : ℝ := 1 / (2 * ((n : ℝ) + 1))
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hn : (n : ℝ) * p ≤ 1 / 2 := by
    dsimp [p]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
    nlinarith
  have hb := one_add_mul_le_pow (a := -p) (by linarith : (-2 : ℝ) ≤ -p) n
  have hb' : 1 - (n : ℝ) * p ≤ (1 - p) ^ n := by
    simpa only [mul_neg, sub_eq_add_neg] using hb
  exact (show (1 / 2 : ℝ) ≤ 1 - (n : ℝ) * p by linarith).trans hb'

theorem geometricHeightLaw_tail_exp_upper (t : ℝ≥0) {d : ℕ} (hd : 1 ≤ d) :
    (geometricHeightLaw t).real {h | d ≤ h} ≤ Real.exp (Real.exp 1 * (t : ℝ) - d) := by
  rw [← PWIT.reaches_probability_eq_geometric_tail t d hd]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  apply (PWIT.reaches_probability_le_firstMoment k t.coe_nonneg).trans
  have hroot : 1 ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have hraw : (t : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) ≤
      Real.sqrt ((k + 1 : ℕ) : ℝ) * ((t : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hroot
  exact hraw.trans (PWIT.generation_intensity_exp_upper (Nat.succ_pos k) t.coe_nonneg)

/-- Uniform in the number of edges, including the zero-edge tree. -/
theorem heightLaw_upper_tail_exp (n : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    (Forward.heightLaw allAttach n).real {h | d ≤ h} ≤
      2 * Real.exp (Real.exp 1 * Real.log (2 * ((n : ℝ) + 1)) - d) := by
  have hindex := upperComparisonTime_index_tail n
  have hmix := geometricHeightLaw_tail_ge (upperComparisonTime n) n d
  have hupper := geometricHeightLaw_tail_exp_upper (upperComparisonTime n) hd
  have hlow := mul_le_mul_of_nonneg_left hindex
    (show 0 ≤ (Forward.heightLaw allAttach n).real {h | d ≤ h} from measureReal_nonneg)
  change (geometricHeightLaw (upperComparisonTime n)).real {h | d ≤ h} ≤
    Real.exp (Real.exp 1 * Real.log (2 * ((n : ℝ) + 1)) - d) at hupper
  nlinarith

noncomputable def upperComparisonCenter (n : ℕ) : ℝ :=
  Real.exp 1 * Real.log (2 * ((n : ℝ) + 1))

theorem upperComparisonCenter_pos (n : ℕ) : 0 < upperComparisonCenter n := by
  unfold upperComparisonCenter
  apply mul_pos (Real.exp_pos _)
  apply Real.log_pos
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem upperComparisonCenter_eq (n : ℕ) :
    upperComparisonCenter n = Real.exp 1 * Real.log ((n : ℝ) + 1) + Real.exp 1 * Real.log 2 := by
  unfold upperComparisonCenter
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) + 1 ≠ 0)]
  ring

/-- Real strict thresholds, with a bound valid even below zero. -/
theorem heightLaw_strict_upper_tail_exp (n : ℕ) (r : ℝ) :
    (Forward.heightLaw allAttach n).real {h | r < (h : ℝ)} ≤
      2 * Real.exp (upperComparisonCenter n - r) := by
  by_cases hr : 0 < r
  · have hd : 1 ≤ ⌈r⌉₊ := Nat.ceil_pos.mpr hr
    have hsub : {h : ℕ | r < (h : ℝ)} ⊆ {h : ℕ | ⌈r⌉₊ ≤ h} := by
      intro h hh
      exact Nat.ceil_le.mpr (le_of_lt hh)
    apply (measureReal_mono hsub).trans ((heightLaw_upper_tail_exp n hd).trans ?_)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact sub_le_sub_left (Nat.le_ceil r) _
  · have hcenter := upperComparisonCenter_pos n
    have he : 1 ≤ Real.exp (upperComparisonCenter n - r) :=
      Real.one_le_exp_iff.mpr (by linarith)
    have hp : (Forward.heightLaw allAttach n).real {h | r < (h : ℝ)} ≤ 1 := measureReal_le_one
    linarith

theorem heightLaw_ae_le_edges (n : ℕ) :
    ∀ᵐ h ∂Forward.heightLaw allAttach n, h ≤ n := by
  simpa [plusCount, allAttach] using
    Forward.heightLaw_height_le_plusCount allAttach n

noncomputable def upperExcessAt (n : ℕ) (a : ℝ) : ℝ :=
  ∫ h : ℕ, max ((h : ℝ) - a) 0 ∂Forward.heightLaw allAttach n

theorem upperExcessAt_integrable (n : ℕ) (a : ℝ) :
    Integrable (fun h : ℕ => max ((h : ℝ) - a) 0) (Forward.heightLaw allAttach n) :=
  Forward.heightLaw_integrable allAttach n _

theorem upperExcessAt_nonneg (n : ℕ) (a : ℝ) : 0 ≤ upperExcessAt n a :=
  integral_nonneg (fun _ => le_max_right _ _)

/-- Integrating the exponential tail uses a finite unit grid, since the actual
`n`-edge tree has height at most `n` almost surely. -/
theorem upperExcessAt_comparisonCenter_le (n : ℕ) :
    upperExcessAt n (upperComparisonCenter n) ≤ 2 / (1 - Real.exp (-1)) := by
  let a := upperComparisonCenter n
  let E (j : ℕ) : Set ℕ := {h | a + (j : ℝ) < (h : ℝ)}
  let I (j : ℕ) : ℕ → ℝ := (E j).indicator (fun _ => 1)
  let ρ : ℝ := Real.exp (-1)
  have ha : 0 ≤ a := (upperComparisonCenter_pos n).le
  have hI (j : ℕ) : Integrable (I j) (Forward.heightLaw allAttach n) :=
    (integrable_const 1).indicator (by measurability)
  have hsum := integrable_finsetSum (Finset.range n) (fun j _ => hI j)
  have hpoint : ∀ᵐ h : ℕ ∂Forward.heightLaw allAttach n,
      max ((h : ℝ) - a) 0 ≤ ∑ j ∈ Finset.range n, I j h := by
    filter_upwards [heightLaw_ae_le_edges n] with h hh
    have hh' : (h : ℝ) ≤ n := by exact_mod_cast hh
    have hg := positivePart_le_grid (L := 1) (by norm_num) n ((h : ℝ) - a)
      (by linarith)
    simp only [one_mul, mul_one] at hg
    have he : (∑ j ∈ Finset.range n, if (j : ℝ) < (h : ℝ) - a then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range n, I j h := by
      apply Finset.sum_congr rfl
      intro j _
      change (if (j : ℝ) < (h : ℝ) - a then (1 : ℝ) else 0) =
        (E j).indicator (fun _ => 1) h
      by_cases hj : (j : ℝ) < (h : ℝ) - a
      · have hm : h ∈ E j := by change a + (j : ℝ) < h; linarith
        rw [ite_eq_left hj, Set.indicator_of_mem hm]
      · have hm : h ∉ E j := by change ¬(a + (j : ℝ) < (h : ℝ)); linarith
        rw [ite_eq_right hj, Set.indicator_of_notMem hm]
    rwa [he] at hg
  have htail (j : ℕ) : (Forward.heightLaw allAttach n).real (E j) ≤ 2 * ρ ^ j := by
    have hh := heightLaw_strict_upper_tail_exp n (a + j)
    have he : Real.exp (a - (a + (j : ℝ))) = ρ ^ j := by
      dsimp [ρ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    change (Forward.heightLaw allAttach n).real (E j) ≤ 2 * Real.exp (a - (a + (j : ℝ))) at hh
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
    _ ≤ ∑ j ∈ Finset.range n, 2 * ρ ^ j := Finset.sum_le_sum (fun j _ => htail j)
    _ = 2 * ∑ j ∈ Finset.range n, ρ ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (1 / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hρ hρ1 n) (by norm_num)
    _ = _ := by dsimp [ρ]; ring

noncomputable def upperExcess (n : ℕ) : ℝ :=
  upperExcessAt n (Real.exp 1 * Real.log ((n : ℝ) + 1))

noncomputable def upperExcessConstant : ℝ :=
  Real.exp 1 * Real.log 2 + 2 / (1 - Real.exp (-1))

theorem upperExcessConstant_pos : 0 < upperExcessConstant := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hden : 0 < 1 - Real.exp (-1 : ℝ) := sub_pos.mpr he
  unfold upperExcessConstant
  positivity

/-- Uniformly bounded positive excess above the first-order center. -/
theorem upperExcess_le (n : ℕ) : upperExcess n ≤ upperExcessConstant := by
  let b := Real.exp 1 * Real.log ((n : ℝ) + 1)
  let c := Real.exp 1 * Real.log 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hab : upperComparisonCenter n = b + c := by
    simpa only [b, c] using upperComparisonCenter_eq n
  have hpoint (h : ℕ) : max ((h : ℝ) - b) 0 ≤ c + max ((h : ℝ) - upperComparisonCenter n) 0 := by
    apply max_le
    · have := le_max_left ((h : ℝ) - upperComparisonCenter n) 0
      linarith
    · exact add_nonneg hc (le_max_right _ _)
  calc
    upperExcess n ≤ ∫ h : ℕ, c + max ((h : ℝ) - upperComparisonCenter n) 0
        ∂Forward.heightLaw allAttach n :=
      integral_mono (upperExcessAt_integrable n b)
        ((integrable_const c).add (upperExcessAt_integrable n (upperComparisonCenter n))) hpoint
    _ = c + upperExcessAt n (upperComparisonCenter n) := by
      rw [integral_add (integrable_const c) (upperExcessAt_integrable n (upperComparisonCenter n)),
        integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul, upperExcessAt]
    _ ≤ c + 2 / (1 - Real.exp (-1)) :=
      add_le_add (le_refl c) (upperExcessAt_comparisonCenter_le n)
    _ = upperExcessConstant := rfl

theorem uniformUpperExcess : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, upperExcess n ≤ C :=
  ⟨upperExcessConstant, upperExcessConstant_pos.le, upperExcess_le⟩

end FreezingGrowth.RRT
