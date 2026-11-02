module

/- Local adaptation of Freezing2/Probability/CompanionModel.lean.
   Original SHA-256: 7486b154f49225ad5a29f6147355a5833ca6a500358839663122236d966df70e.
   This local reuse is Apache-2.0 under the user's explicit authorization
   of 29 October 2026; the sibling repository's global license is unchanged.
   See SCALING_PROVENANCE.md for exact transformations and reuse scope. -/

public import FreezingGrowth.ScalingMaximumLimits
public import FreezingGrowth.ScalingHarmonicAsymptotics

/-!
# The actual attachment/freezing tree law

The existing forward construction uses Boolean signs, whereas the cited
scaling theorem uses integer signs. These lemmas identify their walks, survival
conditions and height scales exactly. The tree law is the iterated uniform-active-vertex law
of Algorithm 1, and its maintained heights equal distances in the finite tree.
No equality with the reverse construction is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FreezingGrowth.Scaling

/-- Encode an integer signed schedule for the companion's Algorithm 1. -/
def companionSchedule (x : ℕ → ℤ) : FreezingGrowth.SignSequence := fun i ↦ decide (x i = 1)

theorem companionSchedule_value (x : ℕ → ℤ) (hx : IsSigned x) {i : ℕ} (hi : 0 < i) :
    (if companionSchedule x i then (1 : ℤ) else -1) = x i := by
  rcases hx i hi with h | h <;> simp [companionSchedule, h]

/-- The two schedule encodings have identical integer populations. -/
theorem companion_activeCount (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    FreezingGrowth.activeCount (companionSchedule x) n = activeCount x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [FreezingGrowth.activeCount_succ, activeCount_succ, ih,
      companionSchedule_value x hx (by omega : 0 < n + 1)]

theorem companion_positiveThrough (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) : FreezingGrowth.PositiveThrough (companionSchedule x) n := by
  intro i hi
  rw [companion_activeCount x hx]
  exact hs i hi

/-- The companion's stopping-time premise follows from the source survival premise. -/
theorem companion_before_extinction (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) :
    (n : ℕ∞) < FreezingGrowth.extinctionTime (companionSchedule x) :=
  (FreezingGrowth.lt_extinctionTime_iff _ _).mpr (companion_positiveThrough x hx hs)

/-- Exact equality of the companion height scale and the paper's up-step harmonic sum. -/
theorem companion_heightScale (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    FreezingGrowth.heightScale (companionSchedule x) n = harmonicUpInterval x 0 n := by
  unfold FreezingGrowth.heightScale harmonicUpInterval
  apply Finset.sum_congr rfl
  intro i _
  simp [companionSchedule, companion_activeCount x hx, one_div]

/-- Algorithm 1's random tree for the original integer-sign triangular array. -/
noncomputable def freezingTreeLaw (x : ℕ → ℕ → ℤ) (n : ℕ) :
    Measure FreezingGrowth.Forward.State :=
  FreezingGrowth.Forward.treeLaw (companionSchedule (x n)) n

instance freezingTreeLaw_probability (x : ℕ → ℕ → ℤ) (n : ℕ) :
    IsProbabilityMeasure (freezingTreeLaw x n) := by
  unfold freezingTreeLaw
  infer_instance

/-- The constructed law is supported on valid finite rooted tree states. -/
theorem freezingTreeLaw_valid (x : ℕ → ℕ → ℤ) (n : ℕ) :
    ∀ᵐ s ∂freezingTreeLaw x n, FreezingGrowth.Forward.ValidAt n s :=
  FreezingGrowth.Forward.treeLaw_valid _ _

/-- The maximum used in the height theorem is the actual maximum root distance
in the finite tree, rather than a separate uncharacterized statistic. -/
theorem treeHeight_le_iff_graph_distance {n : ℕ} {s : FreezingGrowth.Forward.State}
    (hs : FreezingGrowth.Forward.ValidAt n s) (h : ℕ) :
    FreezingGrowth.Forward.treeHeight s ≤ h ↔
      ∀ v : {v // v ∈ s.vertices}, s.tree.dist ⟨0, hs.root_mem⟩ v ≤ h := by
  rw [FreezingGrowth.Forward.treeHeight, Finset.sup_le_iff]
  constructor
  · intro hle v
    rw [← hs.height_eq_tree_dist v]
    exact hle v v.property
  · intro hle v hv
    simpa only [← hs.height_eq_tree_dist ⟨v, hv⟩] using hle ⟨v, hv⟩

end FreezingGrowth.Scaling
