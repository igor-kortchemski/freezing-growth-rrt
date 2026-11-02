module

public import FreezingGrowth.LowPopulationAsymptotic

/-! The integer cutoff and deterministic case split in the proof of Theorem 1.2. -/

@[expose] public section

namespace FreezingGrowth

open Filter
open scoped Topology

/-- The paper's cutoff, represented as an integer to compare with active counts.
It is positive for all sufficiently large attachment counts. -/
noncomputable def populationCutoff (n : ℕ) : ℤ := ⌊(n : ℝ) / (3 * Real.log n)⌋

theorem eventually_populationCutoff_pos : ∀ᶠ n : ℕ in atTop, 0 < populationCutoff n := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) / (n : ℝ) < 1 / 3 :=
    (tendsto_order.mp hlim).2 (1 / 3) (by norm_num)
  filter_upwards [hsmall, eventually_log_ge_one] with n hn hlog
  have hn0 : n ≠ 0 := by intro h; norm_num [h] at hlog
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlogpos : 0 < 3 * Real.log (n : ℝ) := by linarith
  have hprod := (div_lt_iff₀ hnr).mp hn
  have hratio : (1 : ℝ) ≤ (n : ℝ) / (3 * Real.log n) :=
    (le_div_iff₀ hlogpos).mpr (by nlinarith)
  have hfloor : (1 : ℤ) ≤ populationCutoff n := Int.le_floor.mpr (by simpa using hratio)
  omega

/-- The exact-floor inequality used in the printed low-population proof. -/
theorem log_scale_le_div_populationCutoff {n : ℕ}
    (hlog : 1 ≤ Real.log (n : ℝ)) (hr : 0 < populationCutoff n) :
    3 * Real.log (n : ℝ) ≤ (n : ℝ) / (populationCutoff n : ℝ) := by
  have hlogpos : 0 < 3 * Real.log (n : ℝ) := by linarith
  have hrpos : (0 : ℝ) < populationCutoff n := by exact_mod_cast hr
  have hfloor : (populationCutoff n : ℝ) ≤ (n : ℝ) / (3 * Real.log n) :=
    Int.floor_le _
  have hprod := (le_div_iff₀ hlogpos).mp hfloor
  apply (le_div_iff₀ hrpos).mpr
  nlinarith

namespace Word

/-- Every finite profile belongs to one of the two cases in the paper. -/
theorem population_dichotomy (n : ℕ) (xs : Word) :
    (∃ j, 1 ≤ j ∧ j ≤ xs.length ∧ populationCutoff n ≤ activeCount xs.toSigns j) ∨
      (∀ j, 1 ≤ j → j ≤ xs.length → activeCount xs.toSigns j < populationCutoff n) := by
  classical
  by_cases h : ∃ j, 1 ≤ j ∧ j ≤ xs.length ∧ populationCutoff n ≤ activeCount xs.toSigns j
  · exact Or.inl h
  · right
    intro j hjpos hj
    exact lt_of_not_ge (fun he => h ⟨j, hjpos, hj, he⟩)

/-- The printed low case satisfies the cap used by the verified low-case estimates. -/
theorem lowPopulation_of_small_profile {n : ℕ} {xs : Word}
    (h : ∀ j, 1 ≤ j → j ≤ xs.length → activeCount xs.toSigns j < populationCutoff n) :
    LowPopulation n xs := by
  apply lowPopulation_of_floor_cutoff
  intro i hi
  exact h (i + 1) (by omega) (by omega)

end Word
end FreezingGrowth
