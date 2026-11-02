module

public import FreezingGrowth.TwoSeedGraftOrderedSeeds
public import FreezingGrowth.TwoSeedGraftMasterPrefix
public import FreezingGrowth.TwoSeedGraftComponents

/-! The consecutive-size master construction for the third deletion comparison.
Both seed orders are determined by birth labels. The shorter branch replays
one fewer master birth, on the same parent array. -/

@[expose] public section
namespace FreezingGrowth.RemoveAttachTreeCoupling

open MeasureTheory TwoSeedGraft

def longPrefix : Word := [true, true, false]
def shortPrefix : Word := [true, false, true]

structure Sample where
  longInitial : Forward.State
  shortInitial : Forward.State
  master : Forward.State

instance : MeasurableSpace Sample := ⊤
instance : DiscreteMeasurableSpace Sample := ⟨fun _ => trivial⟩

/-- Here the source parameter is `n = k + 1`, so all endpoint cases have
positive source size without natural-subtraction ambiguity. -/
noncomputable def sampleLaw (k : ℕ) : Measure Sample :=
  (Forward.treeLaw longPrefix.toSigns longPrefix.length).bind (fun s =>
    (Forward.treeLaw shortPrefix.toSigns shortPrefix.length).bind (fun t =>
      (Forward.treeLaw RRT.allAttach (k + 2)).map (fun r => ⟨s, t, r⟩)))

noncomputable def longState (k : ℕ) (z : Sample) : Forward.State :=
  replay z.longInitial 3 (birthOrderedFirstSeed z.longInitial)
    (birthOrderedSecondSeed z.longInitial) z.master.parent (k + 1)

noncomputable def shortState (k : ℕ) (z : Sample) : Forward.State :=
  replay z.shortInitial 3 (birthOrderedFirstSeed z.shortInitial)
    (birthOrderedSecondSeed z.shortInitial) z.master.parent k

noncomputable def longContinuation (k : ℕ) (z : Sample) : FiniteMarkov.History Forward.State :=
  replayHistory z.longInitial 3 (birthOrderedFirstSeed z.longInitial)
    (birthOrderedSecondSeed z.longInitial) z.master.parent (k + 1)

noncomputable def shortContinuation (k : ℕ) (z : Sample) : FiniteMarkov.History Forward.State :=
  replayHistory z.shortInitial 3 (birthOrderedFirstSeed z.shortInitial)
    (birthOrderedSecondSeed z.shortInitial) z.master.parent k

end FreezingGrowth.RemoveAttachTreeCoupling
