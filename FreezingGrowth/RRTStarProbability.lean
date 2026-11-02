module

public import FreezingGrowth.RRTUniformDepth
public import FreezingGrowth.FiniteLaw
public import FreezingGrowth.StarComparison

/-!
# The recursive-tree star probability

For the actual uniform-attachment tree with `n` edges, height one has mass
`1 / n!` when `n ≥ 1`. The proof follows the conditional choices of Algorithm 1:
height at most one persists exactly when the next parent is the root.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped ENNReal

namespace Forward

theorem ValidAt.height_eq_zero_iff {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) : s.height v = 0 ↔ v = 0 := by
  constructor
  · intro hh
    by_contra hv0
    have := hs.height_parent v hv hv0
    omega
  · rintro rfl
    exact hs.height_root

theorem transitionLaw_height_le_one {n : ℕ} {s : State} (hs : ValidAt n s)
    (ha : s.active = s.vertices) :
    transitionLaw s (n + 1) true {t | treeHeight t ≤ 1} =
      if treeHeight s ≤ 1 then (s.active.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have hroot : 0 ∈ s.active := ha ▸ hs.root_mem
  have ht : n + 1 ∉ s.vertices := by
    intro hh
    have := hs.vertices_le _ hh
    omega
  rw [transitionLaw_apply s _ _ ⟨0, hroot⟩]
  simp only [Set.mem_ofPred_eq]
  have he : s.active.filter (fun v => treeHeight (step s (n + 1) true v) ≤ 1) =
      if treeHeight s ≤ 1 then {0} else ∅ := by
    ext v
    by_cases hh : treeHeight s ≤ 1
    · simp only [hh, ↓reduceIte, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hv, hg⟩
        rw [step, ite_eq_left hv, ite_eq_left rfl, treeHeight_attach s _ _ ht] at hg
        exact (hs.height_eq_zero_iff (hs.active_subset hv)).mp (by omega)
      · rintro rfl
        refine ⟨hroot, ?_⟩
        simp only [step, hroot, ↓reduceIte, treeHeight_attach s _ _ ht, hs.height_root]
        omega
    · simp only [hh, ↓reduceIte, Finset.mem_filter, Finset.notMem_empty,
        iff_false, not_and]
      intro hv hg
      rw [step, ite_eq_left hv, ite_eq_left rfl, treeHeight_attach s _ _ ht] at hg
      omega
  rw [he]
  split_ifs <;> simp

end Forward

namespace RRT

theorem replicate_heightLaw (n : ℕ) :
    Word.heightLaw (List.replicate n true) = Forward.heightLaw allAttach n := by
  unfold Word.heightLaw
  rw [List.length_replicate]
  apply Forward.heightLaw_congr
  intro i hi
  simp [Word.toSigns_succ, List.getElem?_replicate_of_lt hi, allAttach]

/-- The exact one-step star recurrence, including the initial singleton. -/
theorem height_le_one_mass_succ (n : ℕ) :
    Forward.heightLaw allAttach (n + 1) {h | h ≤ 1} =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * Forward.heightLaw allAttach n {h | h ≤ 1} := by
  simp only [Forward.heightLaw, Measure.map_apply measurable_from_top
    (show MeasurableSet {h : ℕ | h ≤ 1} from by trivial)]
  change Forward.treeLaw allAttach (n + 1) {s | Forward.treeHeight s ≤ 1} =
    ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * Forward.treeLaw allAttach n {s | Forward.treeHeight s ≤ 1}
  rw [Forward.treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ s, ({s : Forward.State | Forward.treeHeight s ≤ 1}).indicator
        (fun _ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) s ∂Forward.treeLaw allAttach n := by
      apply lintegral_congr_ae
      filter_upwards [Forward.treeLaw_valid allAttach n, active_eq_vertices n,
        Forward.treeLaw_counts allAttach n (before_extinction n).le] with s hs ha hc
      have hcard : s.active.card = n + 1 := by
        have hh := hc.1
        rw [activeCount_allAttach] at hh
        omega
      rw [show allAttach (n + 1) = true from rfl,
        Forward.transitionLaw_height_le_one hs ha, hcard]
      by_cases hh : Forward.treeHeight s ≤ 1 <;> simp [hh]
    _ = _ := lintegral_indicator_const (by trivial) _

/-- Height at most one has factorial reciprocal mass even at `n = 0`. -/
theorem height_le_one_mass (n : ℕ) :
    Forward.heightLaw allAttach n {h | h ≤ 1} = (Nat.factorial n : ℝ≥0∞)⁻¹ := by
  induction n with
  | zero => simp [Forward.heightLaw, Forward.treeLaw, Forward.treeHeight_initial]
  | succ n ih =>
    rw [height_le_one_mass_succ, ih, Nat.factorial_succ, Nat.cast_mul]
    exact (ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))).symm

theorem treeHeight_pos {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ s ∂Forward.treeLaw allAttach n, 0 < Forward.treeHeight s := by
  filter_upwards [Forward.treeLaw_valid allAttach n,
    Forward.treeLaw_counts allAttach n (before_extinction n).le] with s hs hc
  have hcard : 1 < s.vertices.card := by
    have hh := hc.2
    have hp : plusCount allAttach n = n := by simp [plusCount, allAttach]
    omega
  obtain ⟨v, hv, hv0⟩ := Finset.exists_mem_ne hcard 0
  have hh := hs.height_parent v hv hv0
  have hle := Forward.height_le_treeHeight hv
  omega

/-- O2: the actual `n`-edge RRT is a star with probability `1/n!`. -/
theorem height_one_mass {n : ℕ} (hn : 1 ≤ n) :
    Forward.heightLaw allAttach n {1} = (Nat.factorial n : ℝ≥0∞)⁻¹ := by
  rw [← height_le_one_mass n]
  simp only [Forward.heightLaw, Measure.map_apply measurable_from_top
    (measurableSet_singleton 1), Measure.map_apply measurable_from_top
    (show MeasurableSet {h : ℕ | h ≤ 1} from by trivial)]
  apply measure_congr
  filter_upwards [treeHeight_pos hn] with s hs
  change (Forward.treeHeight s = 1) = (Forward.treeHeight s ≤ 1)
  apply propext
  omega

theorem height_one_real_mass {n : ℕ} (hn : 1 ≤ n) :
    (Forward.heightLaw allAttach n).real {1} = (1 : ℝ) / (Nat.factorial n : ℝ) := by
  rw [Measure.real, height_one_mass hn]
  simp

end RRT
end FreezingGrowth
