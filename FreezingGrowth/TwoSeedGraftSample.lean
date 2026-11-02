module

public import FreezingGrowth.TwoSeedGraftWord
public import FreezingGrowth.ReversePositionPairs

/-! The common actual old state, ordered active pair and fresh master tree
used by the source's full-tree deletion comparisons. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

structure Sample where
  initial : Forward.State
  first : ℕ
  second : ℕ
  master : Forward.State

instance : MeasurableSpace Sample := ⊤
instance : DiscreteMeasurableSpace Sample := ⟨fun _ => trivial⟩

noncomputable def stateSampleLaw (s : Forward.State) (n : ℕ) : Measure Sample :=
  (uniformRootPair s.active).bind (fun p =>
    (Forward.treeLaw RRT.allAttach (n + 1)).map (fun r => ⟨s, p.1, p.2, r⟩))

noncomputable def sampleLaw (xs : Word) (n : ℕ) : Measure Sample :=
  (Forward.treeLaw xs.toSigns xs.length).bind (fun s => stateSampleLaw s n)

def baselineState (T n : ℕ) (z : Sample) : Forward.State :=
  replay z.initial T z.first z.second z.master.parent n

def longPrefixState (T : ℕ) (z : Sample) : Forward.State :=
  Forward.attach (Forward.freeze z.initial (T + 1) z.second) (T + 2) z.first

/-- Root zero of the master is assigned to the new child in the longer word. -/
def longState (T n : ℕ) (z : Sample) : Forward.State :=
  replay (longPrefixState T z) (T + 2) (T + 2) z.first z.master.parent n

theorem stateSampleLaw_probability (s : Forward.State) (n : ℕ) (hcard : 2 ≤ s.active.card) :
    IsProbabilityMeasure (stateSampleLaw s n) := by
  let := uniformRootPair_isProbabilityMeasure s.active hcard
  unfold stateSampleLaw
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  exact Filter.Eventually.of_forall (fun _ : ℕ × ℕ =>
    Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance)

theorem sampleLaw_probability (xs : Word) (n : ℕ)
    (hcard : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, 2 ≤ s.active.card) :
    IsProbabilityMeasure (sampleLaw xs n) := by
  unfold sampleLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [hcard] with s hs
  exact stateSampleLaw_probability s n hs

end FreezingGrowth.TwoSeedGraft
