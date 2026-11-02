module

public import FreezingGrowth.RRTSplitState
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# The two-component recursive-tree growth kernel

The component edge count is retained as part of the observable. Conditional
on this count, the two local trees have a genuine product law. Updating either
factor uses the existing forward transition, so the identities below preserve
the entire local states, rather than only their heights.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

abbrev Result := ℕ × Forward.State × Forward.State

/-- The actual pure-attachment transition packaged as a measurable kernel. -/
noncomputable def attachmentKernel (t : ℕ) : Kernel Forward.State Forward.State :=
  ⟨fun s => Forward.transitionLaw s t true, measurable_from_top⟩

instance attachmentKernel_markov (t : ℕ) : IsMarkovKernel (attachmentKernel t) :=
  ⟨fun s => Forward.transitionLaw_probability s t true⟩

theorem attachmentKernel_comp (k : ℕ) :
    attachmentKernel (k + 1) ∘ₘ Forward.treeLaw RRT.allAttach k =
      Forward.treeLaw RRT.allAttach (k + 1) := rfl

/-- Independent local recursive trees, with the root component size recorded. -/
noncomputable def componentLaw (k l : ℕ) : Measure Result :=
  ((Forward.treeLaw RRT.allAttach k).prod (Forward.treeLaw RRT.allAttach l)).map
    (Prod.mk k)

instance componentLaw_probability (k l : ℕ) : IsProbabilityMeasure (componentLaw k l) := by
  unfold componentLaw
  exact Measure.isProbabilityMeasure_map_iff measurable_prodMk_left.aemeasurable |>.mpr
    inferInstance

/-- Updating only the first local state leaves the independent second one fixed. -/
noncomputable def leftKernel (k : ℕ) : Kernel (Forward.State × Forward.State) Result :=
  ((attachmentKernel (k + 1)) ∥ₖ Kernel.id).map (Prod.mk (k + 1))

/-- Updating only the second local state retains the first component's size. -/
noncomputable def rightKernel (k l : ℕ) : Kernel (Forward.State × Forward.State) Result :=
  (Kernel.id ∥ₖ attachmentKernel (l + 1)).map (Prod.mk k)

theorem leftKernel_comp (k l : ℕ) :
    leftKernel k ∘ₘ
        ((Forward.treeLaw RRT.allAttach k).prod (Forward.treeLaw RRT.allAttach l)) =
      componentLaw (k + 1) l := by
  rw [leftKernel, ← Measure.map_comp _ _ measurable_prodMk_left,
    ← Measure.prod_comp_left, attachmentKernel_comp]
  rfl

theorem rightKernel_comp (k l : ℕ) :
    rightKernel k l ∘ₘ
        ((Forward.treeLaw RRT.allAttach k).prod (Forward.treeLaw RRT.allAttach l)) =
      componentLaw k (l + 1) := by
  rw [rightKernel, ← Measure.map_comp _ _ measurable_prodMk_left,
    ← Measure.prod_comp_right, attachmentKernel_comp]
  rfl

/-- For two nonempty components, choose the side in proportion to its number
of vertices, then choose its parent uniformly by the actual forward kernel. -/
noncomputable def sizeKernel (k l : ℕ) : Kernel (Forward.State × Forward.State) Result where
  toFun p := (((k + 1 : ℕ) : ℝ≥0∞) / (k + l + 2 : ℕ)) • leftKernel k p +
    (((l + 1 : ℕ) : ℝ≥0∞) / (k + l + 2 : ℕ)) • rightKernel k l p
  measurable' := by
    refine Measurable.add ?_ ?_
    · refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ((leftKernel k).measurable_coe hs).const_mul _
    · refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ((rightKernel k l).measurable_coe hs).const_mul _

/-- The totalized observable transition. Its actual use has `k ≤ n`; on that
support the second component has exactly `n-k` edges. -/
noncomputable def growthKernel (n : ℕ) : Kernel Result Result where
  toFun q := sizeKernel q.1 (n - q.1) q.2
  measurable' := measurable_from_prod_countable_right fun k =>
    (sizeKernel k (n - k)).measurable

/-- The exact product-law evolution; this is the conditional-independence
step in the first-edge split induction. -/
theorem sizeKernel_comp (k l : ℕ) :
    sizeKernel k l ∘ₘ
        ((Forward.treeLaw RRT.allAttach k).prod (Forward.treeLaw RRT.allAttach l)) =
      (((k + 1 : ℕ) : ℝ≥0∞) / (k + l + 2 : ℕ)) • componentLaw (k + 1) l +
      (((l + 1 : ℕ) : ℝ≥0∞) / (k + l + 2 : ℕ)) • componentLaw k (l + 1) := by
  rw [← leftKernel_comp, ← rightKernel_comp]
  ext E hE
  simp only [Measure.bind_apply hE (Kernel.aemeasurable _), Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  change (∫⁻ p, ((sizeKernel k l) p) E ∂_) = _
  simp only [sizeKernel, Kernel.coe_mk, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_left (((leftKernel k).measurable_coe hE).const_mul _),
    lintegral_const_mul _ ((leftKernel k).measurable_coe hE),
    lintegral_const_mul _ ((rightKernel k l).measurable_coe hE)]

theorem growthKernel_comp_componentLaw (n k : ℕ) :
    growthKernel n ∘ₘ componentLaw k (n - k) =
      (((k + 1 : ℕ) : ℝ≥0∞) / (k + (n - k) + 2 : ℕ)) •
        componentLaw (k + 1) (n - k) +
      (((n - k + 1 : ℕ) : ℝ≥0∞) / (k + (n - k) + 2 : ℕ)) •
        componentLaw k (n - k + 1) := by
  change (((Forward.treeLaw RRT.allAttach k).prod
    (Forward.treeLaw RRT.allAttach (n - k))).map (Prod.mk k)).bind (growthKernel n) = _
  rw [Measure.bind_map measurable_prodMk_left.aemeasurable
    (growthKernel n).aemeasurable]
  exact sizeKernel_comp k (n - k)

end FreezingGrowth.RRTSplit
