module

public import FreezingGrowth.RRTDepthPairRecurrence

/-! Sampling two distinct vertex IDs changes the actual depth-difference law
only by removal of the diagonal. Equal depths at different IDs are retained. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory
open scoped Classical ProbabilityTheory ENNReal

noncomputable def treeDistinctDepthDifferenceKernel : ProbabilityTheory.Kernel Forward.State ℤ where
  toFun s := if 2 ≤ s.active.card then
    (uniformRootPair s.active).map (signedDepthDifference s) else Measure.dirac 0
  measurable' := measurable_from_top

instance treeDistinctDepthDifferenceKernel_probability (s : Forward.State) :
    IsProbabilityMeasure (treeDistinctDepthDifferenceKernel s) := by
  change IsProbabilityMeasure (if 2 ≤ s.active.card then _ else _)
  split_ifs with hs
  · have := uniformRootPair_isProbabilityMeasure s.active hs
    infer_instance
  · infer_instance

/-- The actual ordered sample without replacement from one RRT. -/
noncomputable def distinctDepthDifferenceLaw (n : ℕ) : Measure ℤ :=
  (Forward.treeLaw allAttach n).bind treeDistinctDepthDifferenceKernel

instance distinctDepthDifferenceLaw_probability (n : ℕ) :
    IsProbabilityMeasure (distinctDepthDifferenceLaw n) :=
  isProbabilityMeasure_bind treeDistinctDepthDifferenceKernel.measurable.aemeasurable
    (Filter.Eventually.of_forall treeDistinctDepthDifferenceKernel_probability)

noncomputable def treeDistinctDepthDifferenceMean (s : Forward.State) (f : ℤ → ℝ) : ℝ :=
  (∑ uv ∈ s.active.offDiag, f (signedDepthDifference s uv)) /
    (s.active.offDiag.card : ℝ)

theorem treeDistinctDepthDifferenceKernel_integral (s : Forward.State)
    (hs : 2 ≤ s.active.card) (f : ℤ → ℝ) :
    (∫ z, f z ∂treeDistinctDepthDifferenceKernel s) =
      treeDistinctDepthDifferenceMean s f := by
  change (∫ z, f z ∂(if 2 ≤ s.active.card then _ else _)) = _
  rw [ite_eq_left hs, integral_map (by fun_prop) (by fun_prop)]
  unfold uniformRootPair Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    unfold treeDistinctDepthDifferenceMean
    ring
  · intro uv _
    exact (integrable_dirac (by simp)).smul_measure
      (ENNReal.inv_ne_top.mpr (by
        exact_mod_cast (offDiag_nonempty_of_two_le_card hs).card_pos.ne'))

theorem treeDistinctDepthDifferenceKernel_support {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) :
    treeDistinctDepthDifferenceKernel s (Set.Icc (-(n : ℤ)) n) = 1 := by
  change (if 2 ≤ s.active.card then _ else Measure.dirac 0) _ = 1
  split_ifs with hne
  · rw [Measure.map_apply (by fun_prop) (by measurability), uniformRootPair,
      Measure.uniformOfFinset_apply]
    have hf : s.active.offDiag.filter
        (fun uv => signedDepthDifference s uv ∈ Set.Icc (-(n : ℤ)) n) = s.active.offDiag := by
      apply Finset.filter_eq_self.mpr
      intro uv huv
      obtain ⟨hu, hv, _⟩ := Finset.mem_offDiag.mp huv
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
      (by exact_mod_cast (offDiag_nonempty_of_two_le_card hne).card_pos.ne') (by finiteness)
  · simp

theorem distinctDepthDifferenceLaw_support (n : ℕ) :
    ∀ᵐ z ∂distinctDepthDifferenceLaw n, z ∈ Set.Icc (-(n : ℤ)) n := by
  apply (ae_iff_prob_eq_one (by measurability)).mpr
  rw [distinctDepthDifferenceLaw,
    Measure.bind_apply (by measurability) treeDistinctDepthDifferenceKernel.measurable.aemeasurable]
  calc
    _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂Forward.treeLaw allAttach n := by
      apply lintegral_congr_ae
      filter_upwards [Forward.treeLaw_valid allAttach n] with s hs
      exact treeDistinctDepthDifferenceKernel_support hs
    _ = 1 := by simp

theorem distinctDepthDifferenceLaw_integrable (n : ℕ) (f : ℤ → ℝ) :
    Integrable f (distinctDepthDifferenceLaw n) := by
  let C : ℝ := ∑ z ∈ Finset.Icc (-(n : ℤ)) n, |f z|
  apply (integrable_const C).mono' (by fun_prop)
  filter_upwards [distinctDepthDifferenceLaw_support n] with z hz
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun z => |f z|) (fun _ _ => abs_nonneg _)
    (Finset.mem_Icc.mpr hz)

theorem distinctDepthDifferenceLaw_integral {n : ℕ} (hn : 1 ≤ n) (f : ℤ → ℝ) :
    (∫ z, f z ∂distinctDepthDifferenceLaw n) =
      ∫ s, treeDistinctDepthDifferenceMean s f ∂Forward.treeLaw allAttach n := by
  have hi := distinctDepthDifferenceLaw_integrable n f
  unfold distinctDepthDifferenceLaw at hi ⊢
  have hi' : Integrable f ((treeDistinctDepthDifferenceKernel ∘ₖ
      ProbabilityTheory.Kernel.const Unit (Forward.treeLaw allAttach n)) ()) := by
    simpa only [ProbabilityTheory.Kernel.comp_apply,
      ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simp only [ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [Forward.treeLaw_counts allAttach n (before_extinction n).le] with s hs
  have hcZ : (s.active.card : ℤ) = (n : ℤ) + 1 := by
    simpa only [activeCount_allAttach] using hs.1
  exact treeDistinctDepthDifferenceKernel_integral s (by omega) f

/-- The missing diagonal has exactly `card` terms, all with difference zero. -/
theorem sum_signedDepthDifference_offDiag (s : Forward.State) (f : ℤ → ℝ) :
    (∑ uv ∈ s.active.offDiag, f (signedDepthDifference s uv)) =
      (∑ u ∈ s.active, ∑ v ∈ s.active, f ((s.height u : ℤ) - s.height v)) -
        (s.active.card : ℝ) * f 0 := by
  have he : s.active.offDiag =
      (s.active ×ˢ s.active).filter (fun uv => uv.1 ≠ uv.2) := by
    ext uv
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [he, Finset.sum_filter, Finset.sum_product]
  have hp (u v : ℕ) :
      (if u ≠ v then f (signedDepthDifference s (u, v)) else 0) =
        f ((s.height u : ℤ) - s.height v) - (if u = v then f 0 else 0) := by
    by_cases h : u = v
    · subst v
      simp
    · simp [h, signedDepthDifference]
  simp_rw [hp, Finset.sum_sub_distrib]
  simp

theorem treeDepthDifferenceMean_distinct {s : Forward.State}
    (hs : 2 ≤ s.active.card) (f : ℤ → ℝ) :
    treeDepthDifferenceMean s f =
      (1 - 1 / (s.active.card : ℝ)) * treeDistinctDepthDifferenceMean s f +
        (1 / (s.active.card : ℝ)) * f 0 := by
  have hc : (s.active.card : ℝ) ≥ 2 := by exact_mod_cast hs
  have hc0 : (s.active.card : ℝ) ≠ 0 := by linarith
  have hc1 : (s.active.card : ℝ) - 1 ≠ 0 := by linarith
  unfold treeDepthDifferenceMean treeDistinctDepthDifferenceMean
  rw [sum_signedDepthDifference_offDiag, card_offDiag_real s.active (by omega)]
  field_simp
  ring

/-- Exact same-tree with/without replacement comparison for every real test. -/
theorem depthDifferenceLaw_integral_distinct {n : ℕ} (hn : 1 ≤ n) (f : ℤ → ℝ) :
    (∫ z, f z ∂depthDifferenceLaw n) =
      (1 - 1 / ((n : ℝ) + 1)) * (∫ z, f z ∂distinctDepthDifferenceLaw n) +
        (1 / ((n : ℝ) + 1)) * f 0 := by
  rw [depthDifferenceLaw_integral, distinctDepthDifferenceLaw_integral hn]
  have he : ∀ᵐ s ∂Forward.treeLaw allAttach n,
      treeDepthDifferenceMean s f =
        (1 - 1 / ((n : ℝ) + 1)) * treeDistinctDepthDifferenceMean s f +
          (1 / ((n : ℝ) + 1)) * f 0 := by
    filter_upwards [Forward.treeLaw_counts allAttach n (before_extinction n).le] with s hs
    have hcZ : (s.active.card : ℤ) = (n : ℤ) + 1 := by
      simpa only [activeCount_allAttach] using hs.1
    have hcR : (s.active.card : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hcZ
    simpa only [hcR] using treeDepthDifferenceMean_distinct (by omega : 2 ≤ s.active.card) f
  rw [integral_congr_ae he,
    integral_add ((Forward.treeLaw_integrable_state allAttach n _).const_mul _) (integrable_const _),
    integral_const_mul, integral_const]
  simp

theorem depthDifferenceLaw_distinct_test_error {n : ℕ} (hn : 1 ≤ n)
    (f : ℤ → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |(∫ z, f z ∂depthDifferenceLaw n) - (∫ z, f z ∂distinctDepthDifferenceLaw n)| ≤
      2 / ((n : ℝ) + 1) := by
  have hi : |∫ z, f z ∂distinctDepthDifferenceLaw n| ≤ 1 := by
    calc
      _ ≤ ∫ z, |f z| ∂distinctDepthDifferenceLaw n := abs_integral_le_integral_abs
      _ ≤ ∫ _z : ℤ, (1 : ℝ) ∂distinctDepthDifferenceLaw n :=
        integral_mono (distinctDepthDifferenceLaw_integrable n _) (integrable_const 1) hf
      _ = 1 := by simp
  rw [depthDifferenceLaw_integral_distinct hn]
  have he :
      (1 - 1 / ((n : ℝ) + 1)) * (∫ z, f z ∂distinctDepthDifferenceLaw n) +
        (1 / ((n : ℝ) + 1)) * f 0 - (∫ z, f z ∂distinctDepthDifferenceLaw n) =
      (f 0 - (∫ z, f z ∂distinctDepthDifferenceLaw n)) / ((n : ℝ) + 1) := by ring
  rw [he, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (abs_sub _ _).trans (by linarith [hf 0])

end FreezingGrowth.RRT
