module

public import FreezingGrowth.MainStatements
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# The minima in Theorem 1.2

Each admissible family is finite and nonempty. Consequently its real-valued
observables attain their infimum. The uniform formulations of the main targets
are exactly the paper's statements about these actual minima. These equivalence
theorems do not prove the main targets.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory Filter
open scoped Topology

namespace Word

/-- The minimum of an observable over all admissible words with `n` attachments. -/
noncomputable def familyMinimum (n : ℕ) (f : Word → ℝ) : ℝ :=
  sInf (f '' {xs : Word | InFamily n xs})

/-- Nonemptiness and finiteness justify the minimum, including at `n = 0`. -/
theorem familyMinimum_attained (n : ℕ) (f : Word → ℝ) :
    ∃ xs : Word, InFamily n xs ∧ familyMinimum n f = f xs ∧
      ∀ ys : Word, InFamily n ys → f xs ≤ f ys := by
  obtain ⟨xs, hx, hm⟩ := Set.exists_min_image {xs : Word | InFamily n xs} f
    (family_finite n) (family_nonempty n)
  have hl : IsLeast (f '' {xs : Word | InFamily n xs}) (f xs) := by
    refine ⟨⟨xs, hx, rfl⟩, ?_⟩
    rintro _ ⟨ys, hy, rfl⟩
    exact hm ys hy
  exact ⟨xs, hx, hl.csInf_eq, hm⟩

theorem familyMinimum_le {n : ℕ} (f : Word → ℝ) {xs : Word}
    (hx : InFamily n xs) : familyMinimum n f ≤ f xs := by
  obtain ⟨ys, _, he, hm⟩ := familyMinimum_attained n f
  rw [he]
  exact hm xs hx

theorem le_familyMinimum_iff (n : ℕ) (f : Word → ℝ) (c : ℝ) :
    c ≤ familyMinimum n f ↔ ∀ xs : Word, InFamily n xs → c ≤ f xs := by
  constructor
  · intro hc xs hx
    exact hc.trans (familyMinimum_le f hx)
  · intro h
    obtain ⟨xs, hx, he, _⟩ := familyMinimum_attained n f
    rw [he]
    exact h xs hx

end Word

/-- The genuine minimum probability displayed in Theorem 1.2. -/
noncomputable def minimumHeightProbability (n : ℕ) : ℝ :=
  Word.familyMinimum n (fun xs => xs.heightLaw.real {h : ℕ | mainThreshold n ≤ (h : ℝ)})

theorem minimumHeightProbability_le_one (n : ℕ) : minimumHeightProbability n ≤ 1 := by
  obtain ⟨xs, hx⟩ := Word.family_nonempty n
  exact (Word.familyMinimum_le _ hx).trans measureReal_le_one

/-- Exact translation of the paper's minimum-probability limit. -/
theorem uniformHeightProbabilityClaim_iff_minimum_tendsto :
    UniformHeightProbabilityClaim ↔ Tendsto minimumHeightProbability atTop (𝓝 1) := by
  constructor
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨N, hN⟩ := h ((1 - a) / 2) (by linarith)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hb : 1 - (1 - a) / 2 ≤ minimumHeightProbability n :=
        (Word.le_familyMinimum_iff n _ _).mpr (hN n hn)
      linarith
    · intro b hb
      exact Filter.Eventually.of_forall (fun n => (minimumHeightProbability_le_one n).trans_lt hb)
  · intro h ε hε
    have he : ∀ᶠ n : ℕ in atTop, 1 - ε < minimumHeightProbability n :=
      (tendsto_order.mp h).1 (1 - ε) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    refine ⟨N, fun n hn xs hx => ?_⟩
    exact (hN n hn).le.trans (Word.familyMinimum_le _ hx)

/-- Exact translation of the paper's eventual minimum-expectation inequality. -/
theorem uniformHeightExpectationClaim_iff_minimum_eventually :
    UniformHeightExpectationClaim ↔
      ∀ᶠ n : ℕ in atTop, mainThreshold n ≤ Word.familyMinimum n Word.expectedHeight := by
  simp only [UniformHeightExpectationClaim, eventually_atTop, Word.le_familyMinimum_iff]

end FreezingGrowth
