module

public import FreezingGrowth.PWIT.AllRankLeading
public import FreezingGrowth.PWIT.AllRankMoment
public import FreezingGrowth.RRTLowerSeed

/-! Assembling the clock seed from a genuine global square-moment bound.
The square-moment bound is a visible premise until the overlap estimate is
supplied. This implication alone does not prove the seed or Theorem 1.2. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Filter

@[fun_prop] theorem measurable_exactLeadingWindowCount (d : ℕ) :
    Measurable (exactLeadingWindowCount d) :=
  (measurable_pathEventCount d (measurableSet_endpointLeadingEvent measurableSet_Ioc)).ennreal_toReal

theorem exactLeadingWindowCount_nonneg (d : ℕ) (ω : Sample) :
    0 ≤ exactLeadingWindowCount d ω := ENNReal.toReal_nonneg

theorem integrable_exactLeadingWindowCount {d : ℕ} (hd : 0 < d) :
    Integrable (exactLeadingWindowCount d) law := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  unfold exactLeadingWindowCount
  apply integrable_pathEventCount_toReal k
    (measurableSet_endpointLeadingEvent measurableSet_Ioc)
    (t := timeCenter (k + 1)) (by unfold timeCenter; positivity)
  intro v _ ω hω
  exact hω.1.2

theorem exactLeadingWindowCount_pos_subset_reaches (d : ℕ) :
    {ω | 0 < exactLeadingWindowCount d ω} ⊆ reaches d (timeCenter d) := by
  intro ω hω
  have hh : 0 < pathEventCount d
      (endpointLeadingEvent (Set.Ioc (timeCenter d - 1) (timeCenter d))) ω :=
    (ENNReal.toReal_pos_iff.mp hω).1
  obtain ⟨v, hv, he⟩ := (pathEventCount_pos_iff _ _ _).mp hh
  exact ⟨v, hv, he.1.2⟩

/-- The quantitative global second moment is the only remaining premise here.
All probability, measurability and integrability transports concern actual
PWIT paths; the resulting seed has no time shift. -/
theorem clockLowerSeed_of_exactLeadingSecondMoment
    (hbound : ∃ B : ℝ, 0 < B ∧ ∀ᶠ d : ℕ in atTop,
      Integrable (fun ω => exactLeadingWindowCount d ω ^ 2) law ∧
        (∫ ω, exactLeadingWindowCount d ω ^ 2 ∂law) ≤ B) : ClockLowerSeed := by
  obtain ⟨B, hB, hbound⟩ := hbound
  obtain ⟨c, hc, hfirst⟩ := eventually_exactLeadingWindowCount_mean_pos
  have hevent : ∀ᶠ d : ℕ in atTop, 1 ≤ d ∧
      c ≤ (∫ ω, exactLeadingWindowCount d ω ∂law) ∧
      Integrable (fun ω => exactLeadingWindowCount d ω ^ 2) law ∧
        (∫ ω, exactLeadingWindowCount d ω ^ 2 ∂law) ≤ B := by
    filter_upwards [eventually_ge_atTop 1, hfirst, hbound] with d hd hmean hsq
    exact ⟨hd, hmean, hsq⟩
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp hevent
  let p : ℝ := min 1 (c ^ 2 / B)
  have hp : 0 < p := by dsimp [p]; positivity
  refine ⟨p, 0, d₀, hp, min_le_left _ _, ?_⟩
  intro d hd
  obtain ⟨hd1, hmean, hsq, hsecond⟩ := hd₀ d hd
  let C : ℝ := B / c
  have hC : 0 < C := div_pos hB hc
  have hboundC : (∫ ω, exactLeadingWindowCount d ω ^ 2 ∂law) ≤
      C * ∫ ω, exactLeadingWindowCount d ω ∂law := by
    apply hsecond.trans
    have hh := mul_le_mul_of_nonneg_left hmean hC.le
    have he : C * c = B := by dsimp [C]; field_simp
    rwa [he] at hh
  have hprob := probability_pos_lower_of_moments (measurable_exactLeadingWindowCount d)
    (exactLeadingWindowCount_nonneg d) (integrable_exactLeadingWindowCount (by omega))
    hsq hC hmean hboundC
  have he : c / C = c ^ 2 / B := by dsimp [C]; field_simp
  rw [he] at hprob
  simpa only [add_zero] using (min_le_right 1 (c ^ 2 / B)).trans
    (hprob.trans (measureReal_mono (exactLeadingWindowCount_pos_subset_reaches d)))

end FreezingGrowth.PWIT
