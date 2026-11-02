module

/- The negative-MGF and Bennett-tail proofs are adapted from the local
   freezing1 companion project's ForwardMaximum.lean (Apache-2.0).
   See NOTICE for provenance. -/

public import FreezingGrowth.Height
public import FreezingGrowth.ForwardHeight
public import FreezingGrowth.BernoulliConcentration

/-!
# Finite height lower bounds from the forward process

The low-values argument in `main.tex`, lines 917–945, compares the maximum
height with a uniform active height. We obtain its expectation and exponential
lower-tail estimates directly from the forward transition recursion. This
does not assert the separate Bernoulli representation or binomial stochastic
domination stated in the manuscript.

These bounds require a nonempty active population, expressed by `n < τ`.
The final extinction step is treated separately by `heightLaw_succ_freeze`.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

/-- A cap on the post-attachment population bounds every Bernoulli mean below.
This is the deterministic input to the low-profile estimate. -/
theorem plusCount_div_le_heightScale {x : SignSequence} {n : ℕ} {r : ℝ}
    (_hr : 0 < r) (h : PositiveThrough x n)
    (hcap : ∀ i < n, x (i + 1) = true → (activeCount x (i + 1) : ℝ) ≤ r) :
    (plusCount x n : ℝ) / r ≤ heightScale x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (h.mono (Nat.le_succ n)) (fun i hi hx => hcap i (by omega) hx)
    rw [plusCount_succ, heightScale_succ]
    cases hx : x (n + 1)
    · simpa [hx] using hi
    · simp only [↓reduceIte, Nat.cast_add, Nat.cast_one]
      have hs : 0 < (activeCount x (n + 1) : ℝ) := by
        exact_mod_cast h (n + 1) le_rfl
      have hb := one_div_le_one_div_of_le hs (hcap n (by omega) hx)
      rw [add_div]
      exact add_le_add hi hb

namespace Forward

/-- Every maintained vertex height is bounded by the number of elapsed steps. -/
theorem ValidAt.treeHeight_le {n : ℕ} {s : State} (hs : ValidAt n s) :
    treeHeight s ≤ n := by
  apply Finset.sup_le
  intro v hv
  exact (hs.height_le_id v hv).trans (hs.vertices_le v hv)

/-- The finite height range makes every real test function integrable. -/
theorem treeLaw_integrable_heightTest (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    Integrable (fun s => f (treeHeight s)) (treeLaw x n) := by
  let C : ℝ := ∑ k ∈ Finset.range (n + 1), |f k|
  apply (integrable_const C).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_valid x n] with s hs
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hs.treeHeight_le))

/-- Integrability also holds on the pushforward distribution of tree height. -/
theorem heightLaw_integrable (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    Integrable f (heightLaw x n) := by
  exact (integrable_map_measure measurable_from_top.aestronglyMeasurable
    measurable_from_top.aemeasurable).mpr (treeLaw_integrable_heightTest x n f)

/-- Integration against the height distribution is integration of the genuine
maximum-distance observable on the forward tree law. -/
theorem heightLaw_integral (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    (∫ k, f k ∂heightLaw x n) = ∫ s, f (treeHeight s) ∂treeLaw x n :=
  integral_map measurable_from_top.aemeasurable
    measurable_from_top.aestronglyMeasurable

/-- The active-height mean is the sum of reciprocal post-attachment populations. -/
theorem uniformActiveHeightLaw_mean (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) :
    (∫ k : ℕ, (k : ℝ) ∂uniformActiveHeightLaw x n) = heightScale x n := by
  induction n with
  | zero =>
    rw [uniformActiveHeightLaw_integral x 0 hτ]
    simp [treeLaw, activeMean, activeSum, initial]
  | succ n ih =>
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
    have hi := ih hnτ
    have hshift : (∫ k : ℕ, ((k + 1 : ℕ) : ℝ) ∂uniformActiveHeightLaw x n) =
        heightScale x n + 1 := by
      simp_rw [Nat.cast_add, Nat.cast_one]
      rw [integral_add (uniformActiveHeightLaw_integrable x n _) (integrable_const 1)]
      simp [hi]
    rw [uniformActiveHeightLaw_integral_succ x n hτ, heightScale_succ]
    cases hx : x (n + 1)
    · simpa [hx] using hi
    · simp only [↓reduceIte, hshift, hi]
      ring

/-- The empirical active mean cannot exceed the maximum over all vertices. -/
theorem activeMean_height_le_treeHeight {s : State} (hs : s.active.Nonempty)
    (hsub : s.active ⊆ s.vertices) :
    activeMean s (fun k => (k : ℝ)) ≤ (treeHeight s : ℝ) := by
  have hc : (0 : ℝ) < s.active.card := by exact_mod_cast hs.card_pos
  rw [activeMean, div_le_iff₀ hc]
  calc
    activeSum s (fun k => (k : ℝ)) ≤ ∑ _v ∈ s.active, (treeHeight s : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      change (s.height v : ℝ) ≤ (treeHeight s : ℝ)
      exact_mod_cast height_le_treeHeight (hsub hv)
    _ = (treeHeight s : ℝ) * s.active.card := by simp [mul_comm]

/-- A genuine expected-height lower bound for the actual forward tree. -/
theorem heightScale_le_expected_treeHeight (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) :
    heightScale x n ≤ ∫ s, (treeHeight s : ℝ) ∂treeLaw x n := by
  rw [← uniformActiveHeightLaw_mean x n hτ, uniformActiveHeightLaw_integral x n hτ]
  apply integral_mono_ae (treeLaw_integrable_activeMean x n _)
    (treeLaw_integrable_heightTest x n _)
  filter_upwards [treeLaw_valid x n, treeLaw_active_nonempty x n hτ] with s hs hne
  exact activeMean_height_le_treeHeight hne hs.active_subset

/-- The low-profile expectation estimate, before the terminal-freeze reduction. -/
theorem profile_expected_lower_bound (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) {r : ℝ} (hr : 0 < r)
    (hcap : ∀ i < n, x (i + 1) = true → (activeCount x (i + 1) : ℝ) ≤ r) :
    (plusCount x n : ℝ) / r ≤ ∫ s, (treeHeight s : ℝ) ∂treeLaw x n :=
  (plusCount_div_le_heightScale hr ((lt_extinctionTime_iff x n).mp hτ) hcap).trans
    (heightScale_le_expected_treeHeight x n hτ)

theorem treeLaw_integrable_exp_treeHeight (x : SignSequence) (n : ℕ) (θ : ℝ) :
    Integrable (fun s => Real.exp (θ * (treeHeight s : ℝ))) (treeLaw x n) :=
  treeLaw_integrable_heightTest x n (fun k => Real.exp (θ * (k : ℝ)))

/-- A uniform active vertex cannot be higher than the tree maximum. -/
theorem exp_treeHeight_le_activeMean {s : State} (hs : s.active.Nonempty)
    (hsub : s.active ⊆ s.vertices) {θ : ℝ} (hθ : θ ≤ 0) :
    Real.exp (θ * (treeHeight s : ℝ)) ≤ activeMean s (fun k => Real.exp (θ * (k : ℝ))) := by
  have hc : (0 : ℝ) < s.active.card := by exact_mod_cast hs.card_pos
  rw [activeMean, le_div_iff₀ hc]
  calc
    Real.exp (θ * (treeHeight s : ℝ)) * s.active.card =
        ∑ _v ∈ s.active, Real.exp (θ * (treeHeight s : ℝ)) := by simp [mul_comm]
    _ ≤ activeSum s (fun k => Real.exp (θ * (k : ℝ))) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ hθ
      exact_mod_cast height_le_treeHeight (hsub hv)

/-- Negative-parameter maximum-height MGF bound from the actual forward dynamics. -/
theorem treeHeight_mgf_negative (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) {θ : ℝ} (hθ : θ ≤ 0) :
    mgf (fun s => (treeHeight s : ℝ)) (treeLaw x n) θ ≤
      Real.exp (heightScale x n * (Real.exp θ - 1)) := by
  calc
    _ ≤ ∫ s, activeMean s (fun k => Real.exp (θ * (k : ℝ))) ∂treeLaw x n := by
      apply integral_mono_ae (treeLaw_integrable_exp_treeHeight x n θ)
        (treeLaw_integrable_activeMean x n _)
      filter_upwards [treeLaw_valid x n, treeLaw_active_nonempty x n hτ] with s hs hne
      exact exp_treeHeight_le_activeMean hne hs.active_subset hθ
    _ = mgf (fun k : ℕ => (k : ℝ)) (uniformActiveHeightLaw x n) θ :=
      (uniformActiveHeightLaw_integral x n hτ _).symm
    _ ≤ _ := uniformActiveHeightLaw_mgf_le x n hτ θ

/-- A Bennett lower-tail estimate centered at any positive lower bound on the
active-height mean. Its scale hypothesis is discharged by a profile cap below. -/
theorem treeHeight_lower_tail_of_scale_lower (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) {q : ℝ} (hq : 0 < q)
    (hscale : q ≤ heightScale x n) {t : ℝ} (ht : 0 < t) :
    (treeLaw x n).real {s | (treeHeight s : ℝ) < q - t} ≤
      Real.exp (-q * bennettRate (t / q)) := by
  let θ := Real.log (1 + t / q)
  have hθ : 0 ≤ θ := Real.log_nonneg (by have := div_pos ht hq; linarith)
  have hcoef : Real.exp (-θ) - 1 ≤ 0 :=
    sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hθ))
  have hmgf : mgf (fun s => (treeHeight s : ℝ)) (treeLaw x n) (-θ) ≤
      Real.exp (q * (Real.exp (-θ) - 1)) :=
    (treeHeight_mgf_negative x n hτ (neg_nonpos.mpr hθ)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hscale hcoef))
  calc
    (treeLaw x n).real {s | (treeHeight s : ℝ) < q - t} ≤
        (treeLaw x n).real {s | (treeHeight s : ℝ) ≤ q - t} :=
      measureReal_mono (by
        intro s hs
        change (treeHeight s : ℝ) < q - t at hs
        change (treeHeight s : ℝ) ≤ q - t
        exact hs.le) (measure_ne_top _ _)
    _ ≤ Real.exp (-(-θ) * (q - t)) * mgf (fun s => (treeHeight s : ℝ)) (treeLaw x n) (-θ) :=
      measure_le_le_exp_mul_mgf _ (neg_nonpos.mpr hθ) (treeLaw_integrable_exp_treeHeight x n (-θ))
    _ ≤ Real.exp (-(-θ) * (q - t)) * Real.exp (q * (Real.exp (-θ) - 1)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ ≤ Real.exp (-θ * (q + t) + q * (Real.exp θ - 1)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (exp_neg_sub_one_add_le hθ) hq.le
      nlinarith
    _ = Real.exp (-q * bennettRate (t / q)) :=
      congrArg Real.exp (bennett_exponent_identity hq ht)

/-- The maximum-height lower tail centered at the exact active-height mean. -/
theorem treeHeight_lower_tail (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (treeLaw x n).real {s | (treeHeight s : ℝ) < heightScale x n - t} ≤
      Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) :=
  treeHeight_lower_tail_of_scale_lower x n hτ
    (heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)) le_rfl ht

/-- The finite lower-tail bound required in the low-profile case, with
`q = number of attachments / population cap`, for the genuine tree law. -/
theorem profile_height_lower_tail (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {r : ℝ} (hr : 0 < r)
    (hcap : ∀ i < n, x (i + 1) = true → (activeCount x (i + 1) : ℝ) ≤ r)
    {t : ℝ} (ht : 0 < t) :
    (treeLaw x n).real {s | (treeHeight s : ℝ) < (plusCount x n : ℝ) / r - t} ≤
      Real.exp (-((plusCount x n : ℝ) / r) * bennettRate (t / ((plusCount x n : ℝ) / r))) := by
  have hp : PositiveThrough x n := (lt_extinctionTime_iff x n).mp hτ
  have hplus : 0 < plusCount x n := by
    have := le_two_mul_plusCount hp
    omega
  exact treeHeight_lower_tail_of_scale_lower x n hτ
    (div_pos (by exact_mod_cast hplus) hr) (plusCount_div_le_heightScale hr hp hcap) ht

end Forward
end FreezingGrowth
