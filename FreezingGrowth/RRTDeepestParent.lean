module

public import FreezingGrowth.RRTHeightIncrement

/-! The sampled parent's depth and height of the same sampled recursive tree. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable def depthHeightKernel : Kernel Forward.State (ℕ × ℕ) where
  toFun s := (Forward.activeHeightKernel s).map (fun h => (h, Forward.treeHeight s))
  measurable' := measurable_from_top

instance depthHeightKernel_probability (s : Forward.State) :
    IsProbabilityMeasure (depthHeightKernel s) := by
  change IsProbabilityMeasure ((Forward.activeHeightKernel s).map _)
  infer_instance

noncomputable def depthHeightLaw (n : ℕ) : Measure (ℕ × ℕ) :=
  (Forward.treeLaw allAttach n).bind depthHeightKernel

instance depthHeightLaw_probability (n : ℕ) : IsProbabilityMeasure (depthHeightLaw n) :=
  isProbabilityMeasure_bind depthHeightKernel.measurable.aemeasurable
    (Filter.Eventually.of_forall depthHeightKernel_probability)

theorem depthHeightLaw_fst (n : ℕ) :
    (depthHeightLaw n).map Prod.fst = uniformVertexDepthLaw n := by
  rw [depthHeightLaw, Measure.map_bind depthHeightKernel.measurable.aemeasurable
    measurable_fst.aemeasurable]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro s
  change ((Forward.activeHeightKernel s).map (fun h => (h, Forward.treeHeight s))).map Prod.fst = _
  rw [Measure.map_map measurable_fst (measurable_of_countable _)]
  simp [Function.comp_def]

theorem meanHeight_increment_eq_deepest_probability (n : ℕ) :
    meanHeight (n + 1) - meanHeight n = (depthHeightLaw n).real {p | p.1 = p.2} := by
  rw [meanHeight_increment_eq_integral]
  let E : Set (ℕ × ℕ) := {p | p.1 = p.2}
  let f : ℕ × ℕ → ℝ := E.indicator (fun _ => 1)
  have hi : Integrable f (depthHeightLaw n) :=
    (integrable_const _).indicator (Set.to_countable _).measurableSet
  have hi' : Integrable f
      ((depthHeightKernel ∘ₖ Kernel.const Unit (Forward.treeLaw allAttach n)) ()) := by
    simpa only [depthHeightLaw, Kernel.comp_apply, Kernel.const_apply] using hi
  have hrec := Kernel.integral_comp hi'
  simp only [Kernel.comp_apply, Kernel.const_apply] at hrec
  calc
    _ = ∫ s, (∫ p, f p ∂depthHeightKernel s) ∂Forward.treeLaw allAttach n := by
      apply integral_congr_ae
      filter_upwards [Forward.treeLaw_active_nonempty allAttach n (before_extinction n)] with s hs
      rw [depthHeightKernel, Kernel.coe_mk,
        integral_map (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aestronglyMeasurable,
        Forward.activeHeightKernel_integral s hs]
      simp only [deepestFraction, f, E, Set.indicator_apply, Set.mem_ofPred_eq]
    _ = ∫ p, f p ∂depthHeightLaw n := hrec.symm
    _ = _ := integral_indicator_one (Set.to_countable _).measurableSet

end FreezingGrowth.RRT
