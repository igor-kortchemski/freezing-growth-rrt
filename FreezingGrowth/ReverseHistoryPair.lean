module

public import FreezingGrowth.ReverseDistinguishedPair
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Fresh delayed pairs and the shortened marginal history

The product measure explicitly samples a fresh pair independently of the
history coordinate. Restricting to avoidance preserves this factorization,
even after a deterministic update of the history alone. The update cannot
depend on the freshly sampled pair. These identities are ingredients for the
joint Algorithm 3 induction, not an assumption that its stored pair is
independent of the full joint history.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

variable {Ω Ω' V : Type*}
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Countable Ω]
  [MeasurableSpace Ω']
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

omit [MeasurableSingletonClass Ω] in
/-- The entire pending subprobability law is a product with the unchanged
history measure. The two-component boundary has zero pending mass. -/
theorem freshPair_avoid_history_factorization (μ : Measure Ω) (s : Finset V)
    {d : V} (hd : d ∈ s) (hs : 2 ≤ s.card) :
    (μ.prod (uniformRootPair s)).restrict (Set.univ ×ˢ avoidsDistinguished d) =
      (((s.card - 2 : ℕ) : ℝ≥0∞) / (s.card : ℝ≥0∞)) •
        μ.prod (uniformRootPair (s.erase d)) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    uniformRootPair_restrict_avoidsDistinguished s hd hs, Measure.prod_smul_right]

/-- Updating only the history preserves independence of the newly stored
pair. In the coupling, `Ω` may already contain an older pair; the fresh pair
is the separate product coordinate and is not an argument of `f`. -/
theorem freshPair_avoid_updated_history_factorization (μ : Measure Ω)
    (f : Ω → Ω') (s : Finset V) {d : V} (hd : d ∈ s) (hs : 2 ≤ s.card) :
    ((μ.prod (uniformRootPair s)).restrict (Set.univ ×ˢ avoidsDistinguished d)).map
        (Prod.map f id) =
      (((s.card - 2 : ℕ) : ℝ≥0∞) / (s.card : ℝ≥0∞)) •
        (μ.map f).prod (uniformRootPair (s.erase d)) := by
  rw [freshPair_avoid_history_factorization μ s hd hs,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable]
  congr 1
  simpa only [Measure.map_id] using
    (Measure.map_prod_map μ (uniformRootPair (s.erase d))
      (measurable_of_countable f) measurable_id).symm

end FreezingGrowth
