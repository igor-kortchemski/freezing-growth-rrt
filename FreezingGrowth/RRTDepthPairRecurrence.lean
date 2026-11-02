module

public import FreezingGrowth.RRTDepthMoments
public import FreezingGrowth.ForwardFiniteSupport
public import FreezingGrowth.ReverseUniformRootPair
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual difference of two recursive-tree vertex depths

The two vertex choices are independent conditional on the same sampled tree.
The diagonal is retained. At an attachment step the both-new-vertex branch
resets the difference to zero; it is not an independent Bernoulli increment.
-/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory
open scoped Classical ProbabilityTheory ENNReal

/-- The signed difference of two observed vertex depths. -/
def signedDepthDifference (s : Forward.State) (uv : ℕ × ℕ) : ℤ :=
  (s.height uv.1 : ℤ) - s.height uv.2

/-- Conditional independent uniform samples from one active vertex set. -/
noncomputable def treeDepthDifferenceKernel : ProbabilityTheory.Kernel Forward.State ℤ where
  toFun s := if s.active.Nonempty then
    ((Measure.uniformOfFinset s.active).prod (Measure.uniformOfFinset s.active)).map
      (signedDepthDifference s)
    else Measure.dirac 0
  measurable' := measurable_from_top

instance treeDepthDifferenceKernel_probability (s : Forward.State) :
    IsProbabilityMeasure (treeDepthDifferenceKernel s) := by
  change IsProbabilityMeasure (if s.active.Nonempty then _ else _)
  split_ifs with hs
  · have := Forward.uniform_active_probability s hs
    infer_instance
  · infer_instance

/-- The actual with-replacement signed depth difference in the RRT with `n` edges. -/
noncomputable def depthDifferenceLaw (n : ℕ) : Measure ℤ :=
  (Forward.treeLaw allAttach n).bind treeDepthDifferenceKernel

instance depthDifferenceLaw_probability (n : ℕ) : IsProbabilityMeasure (depthDifferenceLaw n) :=
  isProbabilityMeasure_bind treeDepthDifferenceKernel.measurable.aemeasurable
    (Filter.Eventually.of_forall treeDepthDifferenceKernel_probability)

theorem uniform_active_prod (s : Forward.State) (hs : s.active.Nonempty) :
    (Measure.uniformOfFinset s.active).prod (Measure.uniformOfFinset s.active) =
      Measure.uniformOfFinset (s.active ×ˢ s.active) := by
  have := Forward.uniform_active_probability s hs
  apply Measure.ext_of_singleton
  intro uv
  have hp := Measure.prod_prod (μ := Measure.uniformOfFinset s.active)
    (ν := Measure.uniformOfFinset s.active) ({uv.1} : Set ℕ) ({uv.2} : Set ℕ)
  simp only [Set.singleton_prod_singleton, Prod.mk.eta] at hp
  rw [hp]
  simp only [Measure.uniformOfFinset_apply_singleton, Finset.mem_product,
    Finset.card_product, Nat.cast_mul]
  split_ifs <;> simp_all
  exact (ENNReal.mul_inv (by simp) (by simp)).symm

private theorem integral_uniform_finset {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    (∫ a, f a ∂Measure.uniformOfFinset s) = (∑ a ∈ s, f a) / s.card := by
  unfold Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast hs.card_pos.ne'))

/-- Finite conditional averaging, before integrating over the random tree. -/
noncomputable def treeDepthDifferenceMean (s : Forward.State) (f : ℤ → ℝ) : ℝ :=
  (∑ u ∈ s.active, ∑ v ∈ s.active, f ((s.height u : ℤ) - s.height v)) /
    (s.active.card : ℝ) ^ 2

theorem treeDepthDifferenceKernel_integral (s : Forward.State)
    (hs : s.active.Nonempty) (f : ℤ → ℝ) :
    (∫ z, f z ∂treeDepthDifferenceKernel s) = treeDepthDifferenceMean s f := by
  change (∫ z, f z ∂(if s.active.Nonempty then _ else _)) = _
  rw [ite_eq_left hs, uniform_active_prod s hs, integral_map (by fun_prop) (by fun_prop),
    integral_uniform_finset _ (hs.product hs)]
  simp only [treeDepthDifferenceMean, signedDepthDifference, Finset.sum_product,
    Finset.card_product, Nat.cast_mul, pow_two]

theorem treeDepthDifferenceKernel_support {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) :
    treeDepthDifferenceKernel s (Set.Icc (-(n : ℤ)) n) = 1 := by
  change (if s.active.Nonempty then _ else Measure.dirac 0) _ = 1
  split_ifs with hne
  · rw [uniform_active_prod s hne, Measure.map_apply (by fun_prop) (by measurability),
      Measure.uniformOfFinset_apply]
    have hf : (s.active ×ˢ s.active).filter
        (fun uv => signedDepthDifference s uv ∈ Set.Icc (-(n : ℤ)) n) =
          s.active ×ˢ s.active := by
      apply Finset.filter_eq_self.mpr
      intro uv huv
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      have hu' := (hs.height_le_id uv.1 (hs.active_subset hu)).trans
        (hs.vertices_le uv.1 (hs.active_subset hu))
      have hv' := (hs.height_le_id uv.2 (hs.active_subset hv)).trans
        (hs.vertices_le uv.2 (hs.active_subset hv))
      change -(n : ℤ) ≤ (s.height uv.1 : ℤ) - s.height uv.2 ∧
        (s.height uv.1 : ℤ) - s.height uv.2 ≤ n
      omega
    simp only [Set.mem_preimage]
    rw [hf]
    exact ENNReal.div_self
      (by exact_mod_cast (hne.product hne).card_pos.ne') (by finiteness)
  · simp

theorem depthDifferenceLaw_support (n : ℕ) :
    ∀ᵐ z ∂depthDifferenceLaw n, z ∈ Set.Icc (-(n : ℤ)) n := by
  apply (ae_iff_prob_eq_one (by measurability)).mpr
  rw [depthDifferenceLaw,
    Measure.bind_apply (by measurability) treeDepthDifferenceKernel.measurable.aemeasurable]
  calc
    _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂Forward.treeLaw allAttach n := by
      apply lintegral_congr_ae
      filter_upwards [Forward.treeLaw_valid allAttach n] with s hs
      exact treeDepthDifferenceKernel_support hs
    _ = 1 := by simp

theorem depthDifferenceLaw_integrable (n : ℕ) (f : ℤ → ℝ) :
    Integrable f (depthDifferenceLaw n) := by
  let C : ℝ := ∑ z ∈ Finset.Icc (-(n : ℤ)) n, |f z|
  apply (integrable_const C).mono' (by fun_prop)
  filter_upwards [depthDifferenceLaw_support n] with z hz
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun z => |f z|) (fun _ _ => abs_nonneg _)
    (Finset.mem_Icc.mpr hz)

/-- This identity identifies the finite average with the actual same-tree law. -/
theorem depthDifferenceLaw_integral (n : ℕ) (f : ℤ → ℝ) :
    (∫ z, f z ∂depthDifferenceLaw n) =
      ∫ s, treeDepthDifferenceMean s f ∂Forward.treeLaw allAttach n := by
  have hi := depthDifferenceLaw_integrable n f
  unfold depthDifferenceLaw at hi ⊢
  have hi' : Integrable f ((treeDepthDifferenceKernel ∘ₖ
      ProbabilityTheory.Kernel.const Unit (Forward.treeLaw allAttach n)) ()) := by
    simpa only [ProbabilityTheory.Kernel.comp_apply,
      ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simp only [ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [Forward.treeLaw_active_nonempty allAttach n (before_extinction n)] with s hs
  exact treeDepthDifferenceKernel_integral s hs f

private theorem pair_sum_insert {α : Type*} [DecidableEq α] (s : Finset α)
    {t : α} (ht : t ∉ s) (g : α → α → ℝ) :
    (∑ u ∈ insert t s, ∑ v ∈ insert t s, g u v) =
      (∑ u ∈ s, ∑ v ∈ s, g u v) + (∑ v ∈ s, g t v) +
        (∑ u ∈ s, g u t) + g t t := by
  simp only [Finset.sum_insert ht, Finset.sum_add_distrib]
  ring

theorem treeDepthDifferenceMean_attach {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) (v : ℕ) (f : ℤ → ℝ) :
    treeDepthDifferenceMean (Forward.attach s (n + 1) v) f =
      ((∑ u ∈ s.active, ∑ w ∈ s.active, f ((s.height u : ℤ) - s.height w)) +
        (∑ w ∈ s.active, f ((s.height v : ℤ) - s.height w + 1)) +
        (∑ u ∈ s.active, f ((s.height u : ℤ) - s.height v - 1)) + f 0) /
          ((s.active.card : ℝ) + 1) ^ 2 := by
  have hfresh : n + 1 ∉ s.active := by
    intro h
    have hh := hs.vertices_le _ (hs.active_subset h)
    omega
  have hold (u : ℕ) (hu : u ∈ s.active) : u ≠ n + 1 := by
    intro he
    exact hfresh (he ▸ hu)
  unfold treeDepthDifferenceMean
  simp only [Forward.attach]
  rw [pair_sum_insert _ hfresh, Finset.card_insert_of_notMem hfresh]
  simp only [Nat.cast_add, Nat.cast_one, Function.update_self, sub_self]
  congr 1
  have h₀ :
      (∑ u ∈ s.active, ∑ w ∈ s.active,
        f (((Function.update s.height (n + 1) (s.height v + 1)) u : ℤ) -
          (Function.update s.height (n + 1) (s.height v + 1)) w)) =
        ∑ u ∈ s.active, ∑ w ∈ s.active, f ((s.height u : ℤ) - s.height w) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro w hw
    simp [Function.update_of_ne (hold u hu), Function.update_of_ne (hold w hw)]
  rw [h₀]
  congr 2
  · congr 1
    apply Finset.sum_congr rfl
    intro w hw
    rw [Function.update_of_ne (hold w hw)]
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro u hu
    rw [Function.update_of_ne (hold u hu)]
    congr 1
    ring

/-- Exact conditional averaging over the uniformly selected parent. -/
theorem average_treeDepthDifferenceMean_attach {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) (hne : s.active.Nonempty) (f : ℤ → ℝ) :
    (∑ v ∈ s.active, treeDepthDifferenceMean (Forward.attach s (n + 1) v) f) /
        s.active.card =
      (1 - 1 / ((s.active.card : ℝ) + 1)) ^ 2 * treeDepthDifferenceMean s f +
      (1 / ((s.active.card : ℝ) + 1)) * (1 - 1 / ((s.active.card : ℝ) + 1)) *
        treeDepthDifferenceMean s (fun z => f (z + 1)) +
      (1 / ((s.active.card : ℝ) + 1)) * (1 - 1 / ((s.active.card : ℝ) + 1)) *
        treeDepthDifferenceMean s (fun z => f (z - 1)) +
      (1 / ((s.active.card : ℝ) + 1)) ^ 2 * f 0 := by
  have hN : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hN' : (s.active.card : ℝ) + 1 ≠ 0 := by positivity
  simp_rw [treeDepthDifferenceMean_attach hs, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hswap :
      (∑ v ∈ s.active, ∑ u ∈ s.active, f ((s.height u : ℤ) - s.height v - 1)) =
        ∑ u ∈ s.active, ∑ v ∈ s.active, f ((s.height u : ℤ) - s.height v - 1) :=
    Finset.sum_comm
  rw [hswap]
  unfold treeDepthDifferenceMean
  field_simp
  ring

/-- Exact actual-law recursion. The last branch is a reset to zero. -/
theorem depthDifferenceLaw_integral_succ (n : ℕ) (f : ℤ → ℝ) :
    (∫ z, f z ∂depthDifferenceLaw (n + 1)) =
      (1 - depthBernoulliParameter n) ^ 2 * (∫ z, f z ∂depthDifferenceLaw n) +
      depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
        (∫ z, f (z + 1) ∂depthDifferenceLaw n) +
      depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
        (∫ z, f (z - 1) ∂depthDifferenceLaw n) +
      depthBernoulliParameter n ^ 2 * f 0 := by
  rw [depthDifferenceLaw_integral,
    Forward.treeLaw_integral_succ_state]
  have he : ∀ᵐ s ∂Forward.treeLaw allAttach n,
      (∫ s', treeDepthDifferenceMean s' f
        ∂Forward.transitionLaw s (n + 1) (allAttach (n + 1))) =
      (1 - depthBernoulliParameter n) ^ 2 * treeDepthDifferenceMean s f +
        depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
          treeDepthDifferenceMean s (fun z => f (z + 1)) +
        depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
          treeDepthDifferenceMean s (fun z => f (z - 1)) +
        depthBernoulliParameter n ^ 2 * f 0 := by
    filter_upwards [Forward.treeLaw_valid allAttach n,
      Forward.treeLaw_counts allAttach n (before_extinction n).le,
      Forward.treeLaw_active_nonempty allAttach n (before_extinction n)] with s hs hc hne
    rw [Forward.transitionLaw_integral s _ _ hne]
    have hstep (v : ℕ) (hv : v ∈ s.active) :
        Forward.step s (n + 1) (allAttach (n + 1)) v =
          Forward.attach s (n + 1) v := by simp [Forward.step, allAttach, hv]
    simp_rw [Finset.sum_congr rfl (fun v hv => congrArg (fun s => treeDepthDifferenceMean s f)
      (hstep v hv))]
    rw [average_treeDepthDifferenceMean_attach hs hne]
    have hcZ : (s.active.card : ℤ) = (n : ℤ) + 1 := by
      simpa only [activeCount_allAttach] using hc.1
    have hcR : (s.active.card : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hcZ
    simp only [hcR, depthBernoulliParameter,
      show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  rw [integral_congr_ae he]
  have h₀ := (Forward.treeLaw_integrable_state allAttach n
    (fun s => treeDepthDifferenceMean s f)).const_mul ((1 - depthBernoulliParameter n) ^ 2)
  have h₁ := (Forward.treeLaw_integrable_state allAttach n
    (fun s => treeDepthDifferenceMean s (fun z => f (z + 1)))).const_mul
      (depthBernoulliParameter n * (1 - depthBernoulliParameter n))
  have h₂ := (Forward.treeLaw_integrable_state allAttach n
    (fun s => treeDepthDifferenceMean s (fun z => f (z - 1)))).const_mul
      (depthBernoulliParameter n * (1 - depthBernoulliParameter n))
  have h₀₁ : Integrable (fun s =>
      (1 - depthBernoulliParameter n) ^ 2 * treeDepthDifferenceMean s f +
        depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
          treeDepthDifferenceMean s (fun z => f (z + 1))) (Forward.treeLaw allAttach n) :=
    Forward.treeLaw_integrable_state allAttach n _
  have h₀₁₂ : Integrable (fun s =>
      (1 - depthBernoulliParameter n) ^ 2 * treeDepthDifferenceMean s f +
        depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
          treeDepthDifferenceMean s (fun z => f (z + 1)) +
        depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
          treeDepthDifferenceMean s (fun z => f (z - 1))) (Forward.treeLaw allAttach n) :=
    Forward.treeLaw_integrable_state allAttach n _
  rw [integral_add h₀₁₂ (integrable_const _),
    integral_add h₀₁ h₂, integral_add h₀ h₁,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [← depthDifferenceLaw_integral, ← depthDifferenceLaw_integral, ← depthDifferenceLaw_integral]

theorem depthDifferenceLaw_integral_neg (n : ℕ) (f : ℤ → ℝ) :
    (∫ z, f (-z) ∂depthDifferenceLaw n) = ∫ z, f z ∂depthDifferenceLaw n := by
  simp_rw [depthDifferenceLaw_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    unfold treeDepthDifferenceMean
    dsimp only
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    omega

end FreezingGrowth.RRT
