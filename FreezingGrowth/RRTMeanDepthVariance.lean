module

public import FreezingGrowth.RRTDepthMoments
public import FreezingGrowth.AbsoluteMomentBounds

/-! The actual random mean depth of a recursive tree has bounded fluctuation.
The proof averages its exact uniform-parent update; no martingale or
independence assertion about two sampled vertices is assumed. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory
open scoped Classical ProbabilityTheory

noncomputable def treeDepthMean (s : Forward.State) : ℝ :=
  Forward.activeMean s (fun k => (k : ℝ))

noncomputable def treeMeanFluctuation (n : ℕ) : ℝ :=
  ∫ s, (treeDepthMean s - depthMean n) ^ 2 ∂Forward.treeLaw allAttach n

theorem treeDepthMean_bound {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s) :
    |treeDepthMean s| ≤ n := by
  apply Forward.activeMean_bound (Nat.cast_nonneg n)
  intro v hv
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (hs.height_le_id v (hs.active_subset hv)).trans
    (hs.vertices_le v (hs.active_subset hv))

theorem integrable_treeMean_power (n : ℕ) (a : ℝ) (r : ℕ) :
    Integrable (fun s => (treeDepthMean s - a) ^ r) (Forward.treeLaw allAttach n) := by
  apply (integrable_const (((n : ℝ) + |a|) ^ r)).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [Forward.treeLaw_valid allAttach n] with s hs
  rw [Real.norm_eq_abs, abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg _) _ r
  exact (abs_sub _ _).trans (add_le_add (treeDepthMean_bound hs) (le_refl _))

private theorem finite_mean_square_update {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (a : ℝ) :
    let N : ℝ := s.card
    let M : ℝ := (∑ i ∈ s, f i) / N
    (∑ i ∈ s, ((M - a) + (f i - M) / (N + 1)) ^ 2) / N =
      (1 - 1 / (N + 1) ^ 2) * (M - a) ^ 2 +
        ((∑ i ∈ s, (f i - a) ^ 2) / N) / (N + 1) ^ 2 := by
  dsimp only
  let N : ℝ := s.card
  let M : ℝ := (∑ i ∈ s, f i) / N
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hs.card_pos
  have hD : 0 < N + 1 := by linarith
  have hzero : ∑ i ∈ s, (f i - M) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    dsimp [M, N]
    field_simp
    ring
  have hp (i : ι) : ((M - a) + (f i - M) / (N + 1)) ^ 2 =
      (1 - 1 / (N + 1) ^ 2) * (M - a) ^ 2 + (f i - a) ^ 2 / (N + 1) ^ 2 +
        (2 * (M - a) * (1 / (N + 1) - 1 / (N + 1) ^ 2)) * (f i - M) := by
    field_simp
    ring
  change (∑ i ∈ s, ((M - a) + (f i - M) / (N + 1)) ^ 2) / N =
    (1 - 1 / (N + 1) ^ 2) * (M - a) ^ 2 +
      ((∑ i ∈ s, (f i - a) ^ 2) / N) / (N + 1) ^ 2
  simp_rw [hp, Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum, hzero, mul_zero, add_zero]
  change (N * ((1 - 1 / (N + 1) ^ 2) * (M - a) ^ 2) +
    (∑ i ∈ s, (f i - a) ^ 2) / (N + 1) ^ 2) / N = _
  field_simp

theorem treeDepthMean_attach_center {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) {v : ℕ} (hv : v ∈ s.active) (a : ℝ) :
    treeDepthMean (Forward.attach s (n + 1) v) - (a + 1 / ((s.active.card : ℝ) + 1)) =
      treeDepthMean s - a + ((s.height v : ℝ) - treeDepthMean s) / (s.active.card + 1) := by
  have hne : s.active.Nonempty := ⟨v, hv⟩
  have hcard : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hfresh : n + 1 ∉ s.active := by
    intro h
    have hh := hs.vertices_le _ (hs.active_subset h)
    omega
  have hsum : Forward.activeSum s (fun k => (k : ℝ)) =
      (s.active.card : ℝ) * treeDepthMean s := by
    unfold treeDepthMean Forward.activeMean
    field_simp
  have he : treeDepthMean (Forward.attach s (n + 1) v) =
      (Forward.activeSum s (fun k => (k : ℝ)) + ((s.height v : ℝ) + 1)) /
        ((s.active.card : ℝ) + 1) := by
    unfold treeDepthMean Forward.activeMean
    rw [Forward.activeSum_attach hs hv]
    simp only [Forward.attach, Finset.card_insert_of_notMem hfresh, Nat.cast_add, Nat.cast_one]
  rw [he, hsum]
  field_simp
  ring

theorem transition_treeMean_square {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) (hne : s.active.Nonempty) (a : ℝ) :
    (∫ s', (treeDepthMean s' - (a + 1 / ((s.active.card : ℝ) + 1))) ^ 2
      ∂Forward.transitionLaw s (n + 1) true) =
      (1 - 1 / ((s.active.card : ℝ) + 1) ^ 2) * (treeDepthMean s - a) ^ 2 +
        Forward.activeMean s (fun k => ((k : ℝ) - a) ^ 2) / (s.active.card + 1) ^ 2 := by
  rw [Forward.transitionLaw_integral s _ _ hne]
  have he (v : ℕ) (hv : v ∈ s.active) :
      (treeDepthMean (Forward.step s (n + 1) true v) - (a + 1 / ((s.active.card : ℝ) + 1))) ^ 2 =
        (treeDepthMean s - a + ((s.height v : ℝ) - treeDepthMean s) / (s.active.card + 1)) ^ 2 := by
    simp only [Forward.step, hv, ↓reduceIte]
    rw [treeDepthMean_attach_center hs hv a]
  rw [Finset.sum_congr rfl he]
  exact finite_mean_square_update s.active hne (fun v => (s.height v : ℝ)) a

private theorem integral_treeLaw_succ_state (n : ℕ) (f : Forward.State → ℝ)
    (hi : Integrable f (Forward.treeLaw allAttach (n + 1))) :
    (∫ s', f s' ∂Forward.treeLaw allAttach (n + 1)) =
      ∫ s, (∫ s', f s' ∂Forward.transitionLaw s (n + 1) true) ∂Forward.treeLaw allAttach n := by
  let K : ProbabilityTheory.Kernel Forward.State Forward.State :=
    ⟨fun s => Forward.transitionLaw s (n + 1) true, measurable_from_top⟩
  rw [Forward.treeLaw] at hi
  have hi' : Integrable f ((K ∘ₖ ProbabilityTheory.Kernel.const Unit
      (Forward.treeLaw allAttach n)) ()) := by
    simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
      ProbabilityTheory.Kernel.const_apply, allAttach] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simpa only [K, Forward.treeLaw, ProbabilityTheory.Kernel.coe_mk,
    ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply, allAttach] using hh

theorem treeMeanFluctuation_zero : treeMeanFluctuation 0 = 0 := by
  simp [treeMeanFluctuation, treeDepthMean, Forward.treeLaw, Forward.activeMean,
    Forward.activeSum, Forward.initial, depthMean]

theorem treeMeanFluctuation_nonneg (n : ℕ) : 0 ≤ treeMeanFluctuation n :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem treeMeanFluctuation_succ (n : ℕ) :
    treeMeanFluctuation (n + 1) =
      (1 - 1 / ((n : ℝ) + 2) ^ 2) * treeMeanFluctuation n +
        depthCenteredMoment n 2 / ((n : ℝ) + 2) ^ 2 := by
  unfold treeMeanFluctuation
  rw [integral_treeLaw_succ_state n _ (integrable_treeMean_power (n + 1) (depthMean (n + 1)) 2)]
  have he : ∀ᵐ s ∂Forward.treeLaw allAttach n,
      (∫ s', (treeDepthMean s' - depthMean (n + 1)) ^ 2
        ∂Forward.transitionLaw s (n + 1) true) =
        (1 - 1 / ((n : ℝ) + 2) ^ 2) * (treeDepthMean s - depthMean n) ^ 2 +
          Forward.activeMean s (fun k => ((k : ℝ) - depthMean n) ^ 2) / ((n : ℝ) + 2) ^ 2 := by
    filter_upwards [Forward.treeLaw_valid allAttach n,
      Forward.treeLaw_counts allAttach n (before_extinction n).le] with s hs hc
    have hcZ : (s.active.card : ℤ) = (n : ℤ) + 1 := by
      simpa only [activeCount_allAttach] using hc.1
    have hcR : (s.active.card : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hcZ
    have hne : s.active.Nonempty := Finset.card_pos.mp (by omega)
    have hh := transition_treeMean_square hs hne (depthMean n)
    simpa only [hcR, depthMean_succ, depthBernoulliParameter,
      show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using hh
  rw [integral_congr_ae he,
    integral_add ((integrable_treeMean_power n (depthMean n) 2).const_mul _)
      ((Forward.treeLaw_integrable_activeMean allAttach n _).div_const _),
    integral_const_mul, integral_div]
  have hm := Forward.uniformActiveHeightLaw_integral allAttach n (before_extinction n)
    (fun k => ((k : ℝ) - depthMean n) ^ 2)
  rw [← hm]
  rfl

/-- The elementary invariant is stronger than the uniform bound one. -/
theorem treeMeanFluctuation_le (n : ℕ) :
    treeMeanFluctuation n ≤ 1 - depthMean n / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [treeMeanFluctuation_zero, depthMean]
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcoef : 0 ≤ 1 - 1 / ((n : ℝ) + 2) ^ 2 := by
      have hh : 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        nlinarith
      linarith
    rw [treeMeanFluctuation_succ]
    calc
      _ ≤ (1 - 1 / ((n : ℝ) + 2) ^ 2) * (1 - depthMean n / ((n : ℝ) + 1)) +
          depthMean n / ((n : ℝ) + 2) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left ih hcoef)
          (div_le_div_of_nonneg_right (depthCenteredMoment_two_le_mean n) (by positivity))
      _ = _ := by
        rw [depthMean_succ]
        unfold depthBernoulliParameter
        push_cast
        field_simp
        ring

theorem treeMeanFluctuation_le_one (n : ℕ) : treeMeanFluctuation n ≤ 1 := by
  apply (treeMeanFluctuation_le n).trans
  have hh : 0 ≤ depthMean n / ((n : ℝ) + 1) :=
    div_nonneg (depthMean_nonneg n) (by positivity)
  linarith

theorem integral_abs_treeDepthMean_sub_mean_le_one (n : ℕ) :
    (∫ s, |treeDepthMean s - depthMean n| ∂Forward.treeLaw allAttach n) ≤ 1 := by
  apply integral_abs_le_one_of_sq_le_one
    (by simpa only [pow_one] using integrable_treeMean_power n (depthMean n) 1)
    (integrable_treeMean_power n (depthMean n) 2)
  exact treeMeanFluctuation_le_one n

end FreezingGrowth.RRT
