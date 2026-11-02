module

public import FreezingGrowth.AlternatingStarProbability
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The lower bound asserted for the attachment count in open question (3)

Open question (3) asks for the smallest `N_n` such that the height of the `n`-edge
recursive tree is stochastically dominated by the height of every tree with `N_n`
attachments. The text asserts, as a consequence of the star probabilities, that
`liminf N_n / (n log_2 n) ≥ 1`. The question itself stays open; only this asserted
consequence is proved here, for every sequence `N` with the domination property
(in particular for the least such `N_n`).
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory Filter
open scoped ENNReal

/-- The asserted consequence in open question (3), in its quantitative form:
every sequence `N` such that each `n`-edge recursive tree is dominated by every tree
with `N n` attachments satisfies, for each `ε > 0`, eventually
`N n ≥ (1 - ε) · n · log₂ n`. This is `liminf N_n / (n log₂ n) ≥ 1`. -/
def Question3LowerBoundClaim : Prop :=
  ∀ N : ℕ → ℕ,
    (∀ n : ℕ, 1 ≤ n → ∀ xs : Word, Word.InFamily (N n) xs →
      Word.HeightLE (List.replicate n true) xs) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 - ε) * ((n : ℝ) * Real.logb 2 n) ≤ N n

namespace Alternating

/-- The star event has mass `2^{-(N-1)}` for every `N`, with the empty word included. -/
theorem heightLaw_le_one_real (N : ℕ) :
    (alternatingWord N).heightLaw.real {h | h ≤ 1} = (1 : ℝ) / ((2 ^ (N - 1) : ℕ) : ℝ) := by
  cases N with
  | zero =>
    have h0 : alternatingWord 0 = List.replicate 0 true := rfl
    rw [h0, Measure.real, RRT.replicate_heightLaw, RRT.height_le_one_mass]
    simp
  | succ N =>
    rw [Measure.real, height_le_one_mass]
    simp

/-- Domination of the `n`-edge recursive tree by the alternating tree with `N` edges
forces `n! ≤ 2^{N-1}`, by comparing the probabilities of being a star. -/
theorem factorial_le_two_pow_of_heightLE {n N : ℕ}
    (hdom : Word.HeightLE (List.replicate n true) (alternatingWord N)) :
    Nat.factorial n ≤ 2 ^ (N - 1) := by
  have htail := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (hdom 2)
  change (Word.heightLaw (List.replicate n true)).real {h | 2 ≤ h} ≤
    (alternatingWord N).heightLaw.real {h | 2 ≤ h} at htail
  have hcomp : {h : ℕ | 2 ≤ h} = {h : ℕ | h ≤ 1}ᶜ := by ext h; simp; omega
  rw [RRT.replicate_heightLaw, hcomp, measureReal_compl (by trivial),
    measureReal_compl (by trivial), probReal_univ, probReal_univ] at htail
  have hr : (Forward.heightLaw RRT.allAttach n).real {h | h ≤ 1} =
      (1 : ℝ) / (Nat.factorial n : ℝ) := by
    rw [Measure.real, RRT.height_le_one_mass]
    simp
  rw [hr, heightLaw_le_one_real N] at htail
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hpow : (0 : ℝ) < ((2 ^ (N - 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (pow_pos (by decide : 0 < (2 : ℕ)) _)
  have h1 : (1 : ℝ) / ((2 ^ (N - 1) : ℕ) : ℝ) ≤ 1 / (Nat.factorial n : ℝ) := by linarith
  have h2 : (Nat.factorial n : ℝ) ≤ ((2 ^ (N - 1) : ℕ) : ℝ) :=
    (one_div_le_one_div hpow hfac).mp h1
  exact_mod_cast h2

end Alternating

/-- The lower bound asserted in open question (3). -/
theorem question3_lowerBound : Question3LowerBoundClaim := by
  intro N hN ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 / ε ≤ Real.log n :=
    (eventually_ge_atTop 2).and
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 / ε))
  filter_upwards [hev] with n hn
  obtain ⟨hn2, hlogn⟩ := hn
  have hdom := hN n (by omega) (alternatingWord (N n)) (alternatingWord_inFamily (N n))
  generalize N n = M at hdom ⊢
  have hfac := Alternating.factorial_le_two_pow_of_heightLE hdom
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- n log n - n ≤ log n! ≤ (M - 1) log 2
  have hexp := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hnpos.le n
  have hfpos : (0 : ℝ) < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hpow_le : (n : ℝ) ^ n ≤ Real.exp n * (Nat.factorial n : ℝ) := by
    rwa [div_le_iff₀ hfpos] at hexp
  have hlog1 : (n : ℝ) * Real.log n ≤ n + Real.log (Nat.factorial n : ℝ) := by
    have := Real.log_le_log (pow_pos hnpos n) hpow_le
    rwa [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hfpos.ne', Real.log_exp] at this
  have hlog2' : Real.log (Nat.factorial n : ℝ) ≤ ((M - 1 : ℕ) : ℝ) * Real.log 2 := by
    have hle : (Nat.factorial n : ℝ) ≤ (2 : ℝ) ^ (M - 1) := by exact_mod_cast hfac
    have := Real.log_le_log hfpos hle
    rwa [Real.log_pow] at this
  have hNle : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
  have hnε : (n : ℝ) ≤ ε * ((n : ℝ) * Real.log n) := by
    have hl : 1 ≤ ε * Real.log n := by
      have := mul_le_mul_of_nonneg_left hlogn hε.le
      rwa [mul_one_div_cancel hε.ne'] at this
    nlinarith
  have hmain : (1 - ε) * ((n : ℝ) * Real.log n) ≤ (M : ℝ) * Real.log 2 := by
    have h3 : ((M - 1 : ℕ) : ℝ) * Real.log 2 ≤ (M : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hNle hlog2.le
    nlinarith
  have hb : Real.logb 2 n = Real.log n / Real.log 2 := rfl
  rw [hb, show (n : ℝ) * (Real.log n / Real.log 2) = ((n : ℝ) * Real.log n) / Real.log 2 by ring,
    ← mul_div_assoc, div_le_iff₀ hlog2]
  exact hmain

end FreezingGrowth
