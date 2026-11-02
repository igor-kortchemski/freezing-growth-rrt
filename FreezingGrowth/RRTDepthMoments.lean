module

public import FreezingGrowth.RRTUniformDepth
public import FreezingGrowth.ActiveHeightBernoulli

/-!
# Moments of the actual uniform recursive-tree vertex depth

Every moment is integrated against the genuine forward uniform-vertex law.
The exact one-step averaging identity supplies the moment recurrences directly.
-/

@[expose] public section

namespace FreezingGrowth.RRT

open MeasureTheory Filter
open scoped Topology

noncomputable def depthMean (n : ℕ) : ℝ := heightScale allAttach n

noncomputable def depthBernoulliParameter (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

noncomputable def depthCenteredMoment (n r : ℕ) : ℝ :=
  ∫ k : ℕ, ((k : ℝ) - depthMean n) ^ r ∂uniformVertexDepthLaw n

@[simp] theorem depthMean_zero : depthMean 0 = 0 := by simp [depthMean]

theorem depthMean_succ (n : ℕ) :
    depthMean (n + 1) = depthMean n + depthBernoulliParameter n := by
  simp only [depthMean, heightScale_eq_shiftedHarmonic, shiftedHarmonic_succ,
    depthBernoulliParameter]

theorem depthBernoulliParameter_pos (n : ℕ) : 0 < depthBernoulliParameter n := by
  unfold depthBernoulliParameter
  positivity

theorem depthBernoulliParameter_le_half (n : ℕ) : depthBernoulliParameter n ≤ 1 / 2 := by
  unfold depthBernoulliParameter
  exact one_div_le_one_div_of_le (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

theorem depthMean_nonneg (n : ℕ) : 0 ≤ depthMean n := by
  induction n with
  | zero => simp
  | succ n ih => rw [depthMean_succ]; exact add_nonneg ih (depthBernoulliParameter_pos n).le

theorem depthCenteredMoment_integrable (n r : ℕ) :
    Integrable (fun k : ℕ => ((k : ℝ) - depthMean n) ^ r) (uniformVertexDepthLaw n) :=
  Forward.uniformActiveHeightLaw_integrable allAttach n _

theorem uniformVertexDepthLaw_integral_succ (n : ℕ) (f : ℕ → ℝ) :
    (∫ k, f k ∂uniformVertexDepthLaw (n + 1)) =
      (1 - depthBernoulliParameter n) * (∫ k, f k ∂uniformVertexDepthLaw n) +
        depthBernoulliParameter n * (∫ k, f (k + 1) ∂uniformVertexDepthLaw n) := by
  have h := Forward.uniformActiveHeightLaw_integral_succ allAttach n (before_extinction (n + 1)) f
  simpa only [uniformVertexDepthLaw, allAttach, ite_true, activeCount_allAttach,
    Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one,
    depthBernoulliParameter, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using h

theorem uniformVertexDepthLaw_integral_succ_average (n : ℕ) (f : ℕ → ℝ) :
    (∫ k, f k ∂uniformVertexDepthLaw (n + 1)) =
      ∫ k, ((1 - depthBernoulliParameter n) * f k +
        depthBernoulliParameter n * f (k + 1)) ∂uniformVertexDepthLaw n := by
  have hf : Integrable f (uniformVertexDepthLaw n) :=
    Forward.uniformActiveHeightLaw_integrable allAttach n f
  have hf' : Integrable (fun k => f (k + 1)) (uniformVertexDepthLaw n) :=
    Forward.uniformActiveHeightLaw_integrable allAttach n _
  rw [uniformVertexDepthLaw_integral_succ,
    integral_add (hf.const_mul (1 - depthBernoulliParameter n))
      (hf'.const_mul (depthBernoulliParameter n)),
    integral_const_mul, integral_const_mul]

theorem uniformVertexDepthLaw_mean (n : ℕ) :
    (∫ k : ℕ, (k : ℝ) ∂uniformVertexDepthLaw n) = depthMean n := by
  induction n with
  | zero => simp [uniformVertexDepthLaw, Forward.uniformActiveHeightLaw_zero]
  | succ n ih =>
    rw [uniformVertexDepthLaw_integral_succ, depthMean_succ]
    have hshift : (∫ k : ℕ, ((k + 1 : ℕ) : ℝ) ∂uniformVertexDepthLaw n) = depthMean n + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
      have hi : Integrable (fun k : ℕ => (k : ℝ)) (uniformVertexDepthLaw n) :=
        Forward.uniformActiveHeightLaw_integrable allAttach n _
      rw [integral_add hi
        (integrable_const 1), ih, integral_const]
      simp
    rw [ih, hshift]
    ring

theorem integral_centered_depth_eq_zero (n : ℕ) :
    (∫ k : ℕ, ((k : ℝ) - depthMean n) ∂uniformVertexDepthLaw n) = 0 := by
  have hi : Integrable (fun k : ℕ => (k : ℝ)) (uniformVertexDepthLaw n) :=
    Forward.uniformActiveHeightLaw_integrable allAttach n _
  rw [integral_sub hi
    (integrable_const _), uniformVertexDepthLaw_mean, integral_const]
  simp

@[simp] theorem depthCenteredMoment_one (n : ℕ) : depthCenteredMoment n 1 = 0 := by
  simpa only [depthCenteredMoment, pow_one] using integral_centered_depth_eq_zero n

@[simp] theorem depthCenteredMoment_zero (r : ℕ) (hr : r ≠ 0) :
    depthCenteredMoment 0 r = 0 := by
  simp [depthCenteredMoment, uniformVertexDepthLaw, Forward.uniformActiveHeightLaw_zero, hr]

theorem depthCenteredMoment_two_nonneg (n : ℕ) : 0 ≤ depthCenteredMoment n 2 :=
  integral_nonneg fun _ => sq_nonneg _

theorem depthCenteredMoment_four_nonneg (n : ℕ) : 0 ≤ depthCenteredMoment n 4 :=
  integral_nonneg fun _ => by positivity

/-- Exact second central moment recursion for the actual marginal law. -/
theorem depthCenteredMoment_two_succ (n : ℕ) :
    depthCenteredMoment (n + 1) 2 = depthCenteredMoment n 2 +
      depthBernoulliParameter n * (1 - depthBernoulliParameter n) := by
  unfold depthCenteredMoment
  rw [uniformVertexDepthLaw_integral_succ_average]
  calc
    _ = ∫ k : ℕ, (((k : ℝ) - depthMean n) ^ 2 +
        depthBernoulliParameter n * (1 - depthBernoulliParameter n))
          ∂uniformVertexDepthLaw n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        rw [depthMean_succ]
        push_cast
        ring
    _ = _ := by
      rw [integral_add (depthCenteredMoment_integrable n 2) (integrable_const _), integral_const]
      simp

/-- The centered fourth moment requires only the previous second and fourth
moments. The cubic term cancels in the two-point average; the remaining linear
term vanishes after integrating the actual centered first moment. -/
theorem depthCenteredMoment_four_succ (n : ℕ) :
    depthCenteredMoment (n + 1) 4 = depthCenteredMoment n 4 +
      6 * depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
        depthCenteredMoment n 2 +
      depthBernoulliParameter n * (1 - depthBernoulliParameter n) ^ 4 +
      (1 - depthBernoulliParameter n) * depthBernoulliParameter n ^ 4 := by
  let p := depthBernoulliParameter n
  let X : ℕ → ℝ := fun k => (k : ℝ) - depthMean n
  let c : ℝ := p * (1 - p) ^ 4 + (1 - p) * p ^ 4
  have hX : Integrable X (uniformVertexDepthLaw n) :=
    Forward.uniformActiveHeightLaw_integrable allAttach n _
  have hX₂ : Integrable (fun k => X k ^ 2) (uniformVertexDepthLaw n) :=
    depthCenteredMoment_integrable n 2
  have hX₄ : Integrable (fun k => X k ^ 4) (uniformVertexDepthLaw n) :=
    depthCenteredMoment_integrable n 4
  have hpoly (k : ℕ) :
      (1 - p) * ((k : ℝ) - depthMean (n + 1)) ^ 4 +
        p * (((k + 1 : ℕ) : ℝ) - depthMean (n + 1)) ^ 4 =
      X k ^ 4 + (6 * p * (1 - p)) * X k ^ 2 +
        (4 * p * (1 - p) * (1 - 2 * p)) * X k + c := by
    dsimp [X, c, p]
    rw [depthMean_succ]
    push_cast
    ring
  have he : depthCenteredMoment (n + 1) 4 =
      ∫ k, (X k ^ 4 + (6 * p * (1 - p)) * X k ^ 2 +
        (4 * p * (1 - p) * (1 - 2 * p)) * X k + c) ∂uniformVertexDepthLaw n := by
    unfold depthCenteredMoment
    rw [uniformVertexDepthLaw_integral_succ_average]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoly)
  have hterm₂ : Integrable (fun k => (6 * p * (1 - p)) * X k ^ 2)
      (uniformVertexDepthLaw n) := hX₂.const_mul _
  have hterm₁ : Integrable (fun k => (4 * p * (1 - p) * (1 - 2 * p)) * X k)
      (uniformVertexDepthLaw n) := hX.const_mul _
  have hsplit₀ :
      (∫ k, (X k ^ 4 + (6 * p * (1 - p)) * X k ^ 2 +
        (4 * p * (1 - p) * (1 - 2 * p)) * X k + c) ∂uniformVertexDepthLaw n) =
      (∫ k, (X k ^ 4 + (6 * p * (1 - p)) * X k ^ 2 +
        (4 * p * (1 - p) * (1 - 2 * p)) * X k) ∂uniformVertexDepthLaw n) +
        ∫ _k : ℕ, c ∂uniformVertexDepthLaw n := by
    simpa only [Pi.add_apply] using
      integral_add ((hX₄.add hterm₂).add hterm₁) (integrable_const c)
  have hsplit₁ :
      (∫ k, (X k ^ 4 + (6 * p * (1 - p)) * X k ^ 2 +
        (4 * p * (1 - p) * (1 - 2 * p)) * X k) ∂uniformVertexDepthLaw n) =
      (∫ k, (X k ^ 4 + (6 * p * (1 - p)) * X k ^ 2) ∂uniformVertexDepthLaw n) +
        ∫ k, (4 * p * (1 - p) * (1 - 2 * p)) * X k ∂uniformVertexDepthLaw n := by
    simpa only [Pi.add_apply] using integral_add (hX₄.add hterm₂) hterm₁
  have hsplit₂ :
      (∫ k, (X k ^ 4 + (6 * p * (1 - p)) * X k ^ 2) ∂uniformVertexDepthLaw n) =
      (∫ k, X k ^ 4 ∂uniformVertexDepthLaw n) +
        ∫ k, (6 * p * (1 - p)) * X k ^ 2 ∂uniformVertexDepthLaw n := by
    simpa only [Pi.add_apply] using integral_add hX₄ hterm₂
  rw [he, hsplit₀, hsplit₁, hsplit₂, integral_const_mul, integral_const_mul, integral_const]
  have hzero : (∫ k, X k ∂uniformVertexDepthLaw n) = 0 := integral_centered_depth_eq_zero n
  rw [hzero]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
  change depthCenteredMoment n 4 + (6 * p * (1 - p)) * depthCenteredMoment n 2 + c = _
  dsimp [p, c]
  ring

theorem depthCenteredMoment_two_bounds (n : ℕ) :
    depthMean n / 2 ≤ depthCenteredMoment n 2 ∧ depthCenteredMoment n 2 ≤ depthMean n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [depthCenteredMoment_two_succ, depthMean_succ]
    have hp := (depthBernoulliParameter_pos n).le
    have hp' := depthBernoulliParameter_le_half n
    have hprod := mul_nonneg hp (show 0 ≤ 1 / 2 - depthBernoulliParameter n by linarith)
    have hsq := sq_nonneg (depthBernoulliParameter n)
    constructor <;> nlinarith [ih.1, ih.2]

theorem depthCenteredMoment_two_ge_half_mean (n : ℕ) :
    depthMean n / 2 ≤ depthCenteredMoment n 2 := (depthCenteredMoment_two_bounds n).1

theorem depthCenteredMoment_two_le_mean (n : ℕ) :
    depthCenteredMoment n 2 ≤ depthMean n := (depthCenteredMoment_two_bounds n).2

theorem centeredBernoulli_fourth_le_parameter (p : ℝ) :
    p * (1 - p) ^ 4 + (1 - p) * p ^ 4 ≤ p := by
  have h₁ := sq_nonneg p
  have h₂ := sq_nonneg (p * (1 - p))
  nlinarith

/-- A uniform fourth-moment bound in terms of the genuine mean scale. -/
theorem depthCenteredMoment_four_le_mean (n : ℕ) :
    depthCenteredMoment n 4 ≤ 3 * (depthMean n) ^ 2 + depthMean n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [depthCenteredMoment_four_succ, depthMean_succ]
    have hp := (depthBernoulliParameter_pos n).le
    have hvar : depthBernoulliParameter n * (1 - depthBernoulliParameter n) ≤
        depthBernoulliParameter n := by nlinarith [sq_nonneg (depthBernoulliParameter n)]
    have hprod := mul_le_mul hvar (depthCenteredMoment_two_le_mean n)
      (depthCenteredMoment_two_nonneg n) hp
    have hfour := centeredBernoulli_fourth_le_parameter (depthBernoulliParameter n)
    have hsq := sq_nonneg (depthBernoulliParameter n)
    nlinarith

theorem tendsto_depthMean_atTop : Tendsto depthMean atTop atTop := by
  change Tendsto (fun n => heightScale allAttach n) atTop atTop
  exact tendsto_heightScale_atTop (fun _ => allAttach) positive_allAttach

theorem eventually_one_le_depthMean : ∀ᶠ n : ℕ in atTop, 1 ≤ depthMean n :=
  tendsto_depthMean_atTop.eventually (eventually_ge_atTop 1)

theorem depthMean_div_log_tendsto_one :
    Tendsto (fun n : ℕ => depthMean n / Real.log (n : ℝ)) atTop (𝓝 1) :=
  heightScale_div_log_tendsto_one

end FreezingGrowth.RRT
