module

public import FreezingGrowth.RRTLowerSeed
public import FreezingGrowth.PWIT.GlobalSecondMoment

/-! The existing actual clock seed transfers at the critical coefficient
three halves. A fixed spatial offset replaces the logarithmic slack used for
the earlier coefficient-two seed. This is a lower estimate only. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory Filter
open scoped NNReal Topology

noncomputable def criticalSeedIndex (A : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (lowerCenter (3 / 2) n - A)

theorem lowerCenter_two_le_critical (n : ℕ) :
    lowerCenter 2 n ≤ lowerCenter (3 / 2) n := by
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hll : 0 ≤ Real.log (1 + Real.log ((n : ℝ) + 1)) :=
    Real.log_nonneg (by linarith)
  unfold lowerCenter
  linarith

theorem tendsto_lowerCenter_critical : Tendsto (lowerCenter (3 / 2)) atTop atTop :=
  tendsto_atTop_mono lowerCenter_two_le_critical tendsto_lowerCenter_two

theorem tendsto_criticalSeedIndex (A : ℝ) :
    Tendsto (criticalSeedIndex A) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_lowerCenter_critical.eventually_ge_atTop ((b : ℝ) + A)] with n hn
  have hh := Nat.le_ceil (lowerCenter (3 / 2) n - A)
  have hr : (b : ℝ) ≤ (criticalSeedIndex A n : ℝ) := by
    dsimp [criticalSeedIndex]
    linarith
  exact_mod_cast hr

/-- The critical logarithmic correction cancels exactly. The remaining
ceiling and log-scale losses are the fixed constant five halves. -/
theorem criticalSeedIndex_time_upper {A : ℝ} (hA : 1 ≤ A) {n : ℕ}
    (hb : A + 1 ≤ lowerCenter (3 / 2) n) :
    PWIT.timeCenter (criticalSeedIndex A n) ≤
      Real.log ((n : ℝ) + 1) + (5 / 2 - A) / Real.exp 1 := by
  let l : ℝ := Real.log ((n : ℝ) + 1)
  let g : ℝ := Real.log (1 + l)
  let d : ℕ := criticalSeedIndex A n
  have hl : 0 ≤ l := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hg : 0 ≤ g := Real.log_nonneg (by linarith)
  have hcenter : lowerCenter (3 / 2) n = Real.exp 1 * l - (3 / 2) * g := rfl
  have hd : (d : ℝ) < lowerCenter (3 / 2) n - A + 1 := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ lowerCenter (3 / 2) n - A)
    exact hh
  have hdpos : 0 < d := by
    have hh := Nat.le_ceil (lowerCenter (3 / 2) n - A)
    have hr : (1 : ℝ) ≤ d := by dsimp [d, criticalSeedIndex]; linarith
    have hn : 1 ≤ d := by exact_mod_cast hr
    omega
  have hde : (d : ℝ) ≤ Real.exp 1 * l := by rw [hcenter] at hd; linarith
  have hlogd : Real.log (d : ℝ) ≤ 1 + g := by
    have hh := Real.log_le_log (show (0 : ℝ) < d by exact_mod_cast hdpos)
      (show (d : ℝ) ≤ Real.exp 1 * (1 + l) by
        have := Real.exp_pos (1 : ℝ); nlinarith)
    rw [Real.log_mul (Real.exp_ne_zero _) (by linarith : 1 + l ≠ 0), Real.log_exp] at hh
    exact hh
  have hleft : (d : ℝ) / Real.exp 1 + 3 * Real.log d / (2 * Real.exp 1) =
      (2 * (d : ℝ) + 3 * Real.log d) / (2 * Real.exp 1) := by
    field_simp
  have hright : l + (5 / 2 - A) / Real.exp 1 =
      (2 * Real.exp 1 * l + 5 - 2 * A) / (2 * Real.exp 1) := by
    field_simp
    ring
  unfold PWIT.timeCenter
  change (d : ℝ) / Real.exp 1 + 3 * Real.log d / (2 * Real.exp 1) ≤
    l + (5 / 2 - A) / Real.exp 1
  rw [hleft, hright]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * Real.exp 1)).mpr
  rw [hcenter] at hd
  linarith

theorem constantSuccessSeed_critical_of_clockLowerSeed (hs : PWIT.ClockLowerSeed) :
    ConstantSuccessSeed (3 / 2) := by
  obtain ⟨p, K, d₀, hp, hp1, hs⟩ := hs
  have hp2 : 0 < p / 2 := half_pos hp
  have hp21 : p / 2 ≤ 1 := by linarith
  let A : ℝ := max 1 (5 / 2 + Real.exp 1 * (K - Real.log (p / 2)))
  have hA : 1 ≤ A := le_max_left _ _
  have hshift : (5 / 2 - A) / Real.exp 1 + K ≤ Real.log (p / 2) := by
    have ha : 5 / 2 + Real.exp 1 * (K - Real.log (p / 2)) ≤ A := le_max_right _ _
    have hh : (5 / 2 - A) / Real.exp 1 ≤ Real.log (p / 2) - K := by
      apply (div_le_iff₀ (Real.exp_pos 1)).mpr
      nlinarith
    linarith
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hev : ∀ᶠ n : ℕ in atTop,
      lowerTail n (lowerCenter (3 / 2) n - A) ≤ 1 - p / 2 := by
    filter_upwards [(tendsto_criticalSeedIndex A).eventually_ge_atTop (max d₀ 1),
      tendsto_lowerCenter_critical.eventually_ge_atTop (A + 1),
      hlog.eventually_ge_atTop (-Real.log (p / 2))] with n hd hb hnonneg
    let t : ℝ≥0 := ⟨Real.log ((n : ℝ) + 1) + Real.log (p / 2), by linarith⟩
    have hd0 : d₀ ≤ criticalSeedIndex A n := (le_max_left d₀ 1).trans hd
    have hdpos : 0 < criticalSeedIndex A n := by
      have := (le_max_right d₀ 1).trans hd
      omega
    have htime : PWIT.timeCenter (criticalSeedIndex A n) + K ≤ (t : ℝ) := by
      have hh := criticalSeedIndex_time_upper hA hb
      change PWIT.timeCenter (criticalSeedIndex A n) + K ≤
        Real.log ((n : ℝ) + 1) + Real.log (p / 2)
      linarith
    have hclock : p ≤ PWIT.law.real (PWIT.reaches (criticalSeedIndex A n) (t : ℝ)) :=
      (hs _ hd0).trans (measureReal_mono (PWIT.reaches_mono_time htime))
    rw [PWIT.reaches_probability_eq_geometric_tail t _ hdpos] at hclock
    have hexp : Real.exp (t : ℝ) = ((n : ℝ) + 1) * (p / 2) := by
      change Real.exp (Real.log ((n : ℝ) + 1) + Real.log (p / 2)) = _
      rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log hp2]
    have hindex : (geometricIndexLaw t).real {k | n < k} ≤ p / 2 := by
      apply (geometricIndexLaw_tail_le_mean t n).trans
      rw [hexp]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      nlinarith
    have htransfer := geometricHeightLaw_tail_le t n (criticalSeedIndex A n)
    have hheight : p / 2 ≤
        (Forward.heightLaw allAttach n).real {h | criticalSeedIndex A n ≤ h} := by
      linarith
    have he : {h : ℕ | (h : ℝ) < lowerCenter (3 / 2) n - A} =
        {h : ℕ | criticalSeedIndex A n ≤ h}ᶜ := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, criticalSeedIndex, Nat.ceil_le, not_le]
    rw [lowerTail, he, measureReal_compl (Set.to_countable _).measurableSet, probReal_univ]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact constantSuccessSeed_of_eventual (by norm_num : (0 : ℝ) ≤ 3 / 2) hp2 hp21 N hN

/-- The actual recursive tree has a uniform positive success probability at
the critical lower center. No clock estimate remains as a premise. -/
theorem constantSuccessSeed_critical : ConstantSuccessSeed (3 / 2) :=
  constantSuccessSeed_critical_of_clockLowerSeed PWIT.clockLowerSeed

theorem uniformLowerDeficit_critical : UniformLowerDeficit (3 / 2) :=
  uniformLowerDeficit_of_seed (by norm_num) constantSuccessSeed_critical

end FreezingGrowth.RRT
