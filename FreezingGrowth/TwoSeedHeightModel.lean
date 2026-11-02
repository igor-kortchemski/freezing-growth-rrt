module

public import FreezingGrowth.SeedDepthMaximum
public import FreezingGrowth.RRTSplitIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-! A countable joint height model: the old ordered depths and full maximum
keep their actual dependence, while the later recursive-tree split is fresh. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedCoupling

open MeasureTheory
open scoped Classical

abbrev ModelSample := DepthMaximum × (ℕ × ℕ)

noncomputable def heightModelLaw (m n : ℕ) : Measure ModelSample :=
  (depthMaximumLaw m).prod (RRTSplit.heightPairLaw n)

theorem heightModelLaw_probability (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    IsProbabilityMeasure (heightModelLaw m n) := by
  let := depthMaximumLaw_probability m hm
  unfold heightModelLaw
  infer_instance

theorem heightModelLaw_integrable (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (F : ModelSample → ℝ) :
    Integrable F (heightModelLaw m n) := by
  unfold heightModelLaw
  apply (integrable_prod_iff (measurable_of_countable F).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun d => RRTSplit.heightPairLaw_integrable n (fun p => F (d, p)))
  · exact depthMaximumLaw_integrable m hm _

theorem heightModelLaw_integral (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (F : ModelSample → ℝ) :
    (∫ z, F z ∂heightModelLaw m n) =
      ∫ d, (∫ p, F (d, p) ∂RRTSplit.heightPairLaw n) ∂depthMaximumLaw m :=
  integral_prod F (heightModelLaw_integrable m hm n F)

def swapDepthMaximum (d : DepthMaximum) : DepthMaximum := (d.2.1, d.1, d.2.2)

theorem depthMaximumLaw_swap (m : ℕ) (hm : 1 ≤ m) :
    (depthMaximumLaw m).map swapDepthMaximum = depthMaximumLaw m := by
  let := depthMaximumLaw_probability m hm
  let : IsProbabilityMeasure ((depthMaximumLaw m).map swapDepthMaximum) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  apply measures_eq_of_integrals
  intro F
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable]
  simp only [depthMaximumLaw_integral m hm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    dsimp only [swapDepthMaximum]
    unfold Forward.activePairHeightMean FiniteAveraging.distinctPairMean FiniteAveraging.pairSum
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u = v
    · subst v
      simp
    · simp [huv, Ne.symm huv])

def baselineHeight (z : ModelSample) : ℕ :=
  HeightProfile.seedHeight z.1.1 z.1.2.1 z.1.2.2 z.2

/-- Source orientation: the first component is grafted to the new child. -/
def longHeight (z : ModelSample) : ℕ :=
  HeightProfile.seedHeight (z.1.1 + 1) z.1.1 z.1.2.2 z.2

end FreezingGrowth.TwoSeedCoupling
