module

public import FreezingGrowth.RRTSplitComponents
public import FreezingGrowth.RRTSplitLumping

/-!
# The exact first-edge recursive-tree split law

For a recursive tree with `n+1` edges, deletion of its first edge produces
components with edge counts `k` and `n-k`, where `k` is uniform on `0,...,n`.
Their increasing-birth-label local states have the independent recursive-tree
product law conditional on that size. The graph partition and the reset depth
of the second component are established in the imported support theorems.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- Exact joint law of the size and both complete canonically relabelled
components. In particular, conditional independence is in the conclusion. -/
theorem treeLaw_firstEdgeSplit (n : ℕ) :
    (Forward.treeLaw RRT.allAttach (n + 1)).map (firstEdgeSplit n) = mixtureLaw n := by
  induction n with
  | zero =>
    rw [treeLaw_one, Measure.map_dirac' measurable_from_top, mixtureLaw_zero]
    rfl
  | succ n ih =>
    change ((Forward.treeLaw RRT.allAttach (n + 1)).bind
      (fun s => Forward.transitionLaw s (n + 2) true)).map (firstEdgeSplit (n + 1)) = _
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    calc
      _ = (Forward.treeLaw RRT.allAttach (n + 1)).bind
          (fun s => growthKernel n (firstEdgeSplit n s)) := by
        apply Measure.bind_congr_right
        filter_upwards [treeLaw_split_describes n] with s hs
        exact map_transition_split hs
      _ = growthKernel n ∘ₘ
          ((Forward.treeLaw RRT.allAttach (n + 1)).map (firstEdgeSplit n)) := by
        exact (Measure.bind_map measurable_from_top.aemeasurable
          (growthKernel n).aemeasurable).symm
      _ = mixtureLaw (n + 1) := by rw [ih, growthKernel_comp_mixtureLaw]

/-- Source-facing form with every distribution and conditional size visible.
The zero-edge endpoints are singleton rooted trees under the same forward law. -/
theorem first_edge_split_joint_law (n : ℕ) :
    (Forward.treeLaw RRT.allAttach (n + 1)).map (firstEdgeSplit n) =
      (Measure.uniformOfFinset (Finset.range (n + 1))).bind (fun k =>
        ((Forward.treeLaw RRT.allAttach k).prod
          (Forward.treeLaw RRT.allAttach (n - k))).map (fun p => (k, p.1, p.2))) :=
  treeLaw_firstEdgeSplit n

end FreezingGrowth.RRTSplit
