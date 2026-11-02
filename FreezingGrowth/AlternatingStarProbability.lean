module

public import FreezingGrowth.AlternatingHeight
public import FreezingGrowth.RRTStarProbability

/-!
# The alternating-tree star probability

At every even horizon the alternating tree has exactly one active vertex.
For its height to stay at most one, this vertex must still be the root.
Each subsequent freezing preserves that event with probability one half.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped ENNReal

namespace Alternating

def starRoot : Set Forward.State := {s | Forward.treeHeight s ≤ 1 ∧ 0 ∈ s.active}

theorem attach_height_le_one_iff {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) (ha : s.active.card = 1) {v : ℕ} (hv : v ∈ s.active) :
    Forward.treeHeight (Forward.step s (n + 1) true v) ≤ 1 ↔ s ∈ starRoot := by
  have ht : n + 1 ∉ s.vertices := by
    intro h
    have := hs.vertices_le _ h
    omega
  rw [Forward.step, ite_eq_left hv, ite_eq_left rfl, Forward.treeHeight_attach s _ _ ht]
  constructor
  · intro hh
    have hv0 : v = 0 := (hs.height_eq_zero_iff (hs.active_subset hv)).mp (by omega)
    exact ⟨by omega, hv0 ▸ hv⟩
  · rintro ⟨hh, hroot⟩
    have hv0 : v = 0 := (Finset.card_le_one.mp ha.le) v hv 0 hroot
    rw [hv0, hs.height_root]
    omega

theorem attach_starRoot_iff {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) (ha : s.active.card = 1) {v : ℕ} (hv : v ∈ s.active) :
    Forward.step s (n + 1) true v ∈ starRoot ↔ s ∈ starRoot := by
  change (_ ≤ 1 ∧ _) ↔ _
  rw [attach_height_le_one_iff hs ha hv]
  constructor
  · exact And.left
  · intro hh
    refine ⟨hh, ?_⟩
    simp only [Forward.step, hv, ↓reduceIte, Forward.attach, Finset.mem_insert]
    exact Or.inr hh.2

theorem transition_attach_event {n : ℕ} {s : Forward.State}
    (_hs : Forward.ValidAt n s) (ha : s.active.card = 1)
    (E : Set Forward.State)
    (hE : ∀ v ∈ s.active, Forward.step s (n + 1) true v ∈ E ↔ s ∈ starRoot) :
    Forward.transitionLaw s (n + 1) true E = starRoot.indicator (fun _ => 1) s := by
  classical
  rw [Forward.transitionLaw_apply s _ _ (Finset.card_pos.mp (by omega))]
  by_cases hh : s ∈ starRoot
  · have he : s.active.filter (fun v => Forward.step s (n + 1) true v ∈ E) = s.active :=
      Finset.filter_eq_self.mpr (fun v hv => (hE v hv).mpr hh)
    rw [he, ha]
    simp [hh]
  · have he : s.active.filter (fun v => Forward.step s (n + 1) true v ∈ E) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv
      exact fun h => hh ((hE v hv).mp h)
    rw [he]
    simp [hh]

theorem transition_freeze_starRoot (s : Forward.State) (t : ℕ)
    (ha : s.active.card = 2) :
    Forward.transitionLaw s t false starRoot = starRoot.indicator (fun _ => 2⁻¹) s := by
  classical
  rw [Forward.transitionLaw_apply s _ _ (Finset.card_pos.mp (by omega))]
  by_cases hh : s ∈ starRoot
  · have he : s.active.filter (fun v => Forward.step s t false v ∈ starRoot) =
        s.active.erase 0 := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hv, hg⟩
        change Forward.treeHeight _ ≤ 1 ∧ 0 ∈ _ at hg
        have hr : 0 ∈ s.active.erase v := by
          simpa only [Forward.step, hv, Bool.false_eq_true, ↓reduceIte, Forward.freeze] using hg.2
        exact ⟨Ne.symm (Finset.mem_erase.mp hr).1, hv⟩
      · rintro ⟨hv0, hv⟩
        refine ⟨hv, ?_⟩
        simp only [starRoot, Set.mem_ofPred_eq, Forward.step, hv, Bool.false_eq_true, ↓reduceIte,
          Forward.freeze, Finset.mem_erase]
        exact ⟨hh.1, Ne.symm hv0, hh.2⟩
    rw [he, Finset.card_erase_of_mem hh.2, ha]
    simp [hh]
  · have he : s.active.filter (fun v => Forward.step s t false v ∈ starRoot) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv hg
      apply hh
      change Forward.treeHeight _ ≤ 1 ∧ 0 ∈ _ at hg
      simp only [Forward.step, hv, Bool.false_eq_true, ↓reduceIte,
        Forward.freeze, Finset.mem_erase] at hg
      exact ⟨hg.1, hg.2.2⟩
    rw [he]
    simp [hh]

theorem active_card (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw alternatingSigns n,
      s.active.card = if n % 2 = 0 then 1 else 2 := by
  filter_upwards [Forward.treeLaw_counts alternatingSigns n
    (alternating_before_extinction n).le] with s hs
  have hh := hs.1
  rw [alternating_activeCount] at hh
  split_ifs at hh ⊢ <;> omega

theorem attach_mass (n : ℕ) (E : Set Forward.State)
    (hE : ∀ s, Forward.ValidAt (2 * n) s → s.active.card = 1 →
      ∀ v ∈ s.active, Forward.step s (2 * n + 1) true v ∈ E ↔ s ∈ starRoot) :
    Forward.treeLaw alternatingSigns (2 * n + 1) E =
      Forward.treeLaw alternatingSigns (2 * n) starRoot := by
  rw [Forward.treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  have hx : alternatingSigns (2 * n + 1) = true := by simp [alternatingSigns, Nat.add_mod]
  rw [hx]
  calc
    _ = ∫⁻ s, starRoot.indicator (fun _ => 1) s ∂Forward.treeLaw alternatingSigns (2 * n) := by
      apply lintegral_congr_ae
      filter_upwards [Forward.treeLaw_valid alternatingSigns (2 * n), active_card (2 * n)]
        with s hs ha
      have ha' : s.active.card = 1 := by simpa using ha
      exact transition_attach_event hs ha' E (hE s hs ha')
    _ = _ := by rw [lintegral_indicator_const (by trivial)]; simp

theorem freeze_starRoot_mass (n : ℕ) :
    Forward.treeLaw alternatingSigns (2 * (n + 1)) starRoot =
      2⁻¹ * Forward.treeLaw alternatingSigns (2 * n + 1) starRoot := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Forward.treeLaw,
    Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  have hx : alternatingSigns (2 * n + 1 + 1) = false := by
    simp [alternatingSigns, Nat.add_mod]
  rw [hx]
  calc
    _ = ∫⁻ s, starRoot.indicator (fun _ => 2⁻¹) s
        ∂Forward.treeLaw alternatingSigns (2 * n + 1) := by
      apply lintegral_congr_ae
      filter_upwards [active_card (2 * n + 1)] with s ha
      exact transition_freeze_starRoot s _ (by simpa [Nat.add_mod] using ha)
    _ = _ := lintegral_indicator_const (by trivial) _

theorem starRoot_mass (n : ℕ) :
    Forward.treeLaw alternatingSigns (2 * n) starRoot = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  induction n with
  | zero => norm_num [Forward.treeLaw, starRoot, Forward.treeHeight, Forward.initial]
  | succ n ih =>
    rw [freeze_starRoot_mass, attach_mass n starRoot
      (fun _ hs ha _ hv => attach_starRoot_iff hs ha hv), ih, pow_succ]
    rw [ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num))]
    exact mul_comm _ _

/-- O3's cumulative probability before excluding the impossible zero height. -/
theorem height_le_one_mass (n : ℕ) :
    (alternatingWord (n + 1)).heightLaw {h | h ≤ 1} = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [alternatingWord_heightLaw, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Forward.heightLaw_succ_freeze _ _ (by simp [alternatingSigns, Nat.add_mod])]
  rw [Forward.heightLaw, Measure.map_apply measurable_from_top (by trivial)]
  change Forward.treeLaw alternatingSigns (2 * n + 1) {s | Forward.treeHeight s ≤ 1} = _
  rw [attach_mass n _ (fun _ hs ha _ hv => attach_height_le_one_iff hs ha hv), starRoot_mass]

theorem height_le_one_mass_of_pos {n : ℕ} (hn : 1 ≤ n) :
    (alternatingWord n).heightLaw {h | h ≤ 1} = ((2 : ℝ≥0∞) ^ (n - 1))⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa using height_le_one_mass m

theorem treeHeight_pos {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ s ∂Forward.treeLaw alternatingSigns (2 * n), 0 < Forward.treeHeight s := by
  have hp : plusCount alternatingSigns (2 * n) = n := by
    rw [← Word.plusCount_congr (alternatingWord_toSigns n), ← alternatingWord_length n]
    exact alternatingWord_attachments n
  filter_upwards [Forward.treeLaw_valid alternatingSigns (2 * n),
    Forward.treeLaw_counts alternatingSigns (2 * n) (alternating_before_extinction _).le]
    with s hs hc
  have hcard : 1 < s.vertices.card := by rw [hc.2, hp]; omega
  obtain ⟨v, hv, hv0⟩ := Finset.exists_mem_ne hcard 0
  have hh := hs.height_parent v hv hv0
  have hle := Forward.height_le_treeHeight hv
  omega

/-- O3: the actual alternating tree with `n` edges is a star with probability
`2^{-(n-1)}`, including the one-edge boundary. -/
theorem height_one_mass {n : ℕ} (hn : 1 ≤ n) :
    (alternatingWord n).heightLaw {1} = ((2 : ℝ≥0∞) ^ (n - 1))⁻¹ := by
  rw [← height_le_one_mass_of_pos hn, alternatingWord_heightLaw]
  simp only [Forward.heightLaw, Measure.map_apply measurable_from_top
    (measurableSet_singleton 1), Measure.map_apply measurable_from_top
    (show MeasurableSet {h : ℕ | h ≤ 1} from by trivial)]
  apply measure_congr
  filter_upwards [treeHeight_pos hn] with s hs
  change (Forward.treeHeight s = 1) = (Forward.treeHeight s ≤ 1)
  apply propext
  omega

theorem height_one_real_mass {n : ℕ} (hn : 1 ≤ n) :
    (alternatingWord n).heightLaw.real {1} = (1 : ℝ) / (2 ^ (n - 1) : ℕ) := by
  rw [Measure.real, height_one_mass hn]
  simp

/-- Observation 2.1: alternating-tree height does not stochastically dominate
the height of the recursive tree with the same number of edges. -/
theorem not_heightLE_rrt {n : ℕ} (hn : 3 ≤ n) :
    ¬ Word.HeightLE (List.replicate n true) (alternatingWord n) := by
  intro hh
  have htail := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (hh 2)
  change (Word.heightLaw (List.replicate n true)).real {h | 2 ≤ h} ≤
    (alternatingWord n).heightLaw.real {h | 2 ≤ h} at htail
  have hcomp : {h : ℕ | 2 ≤ h} = {h : ℕ | h ≤ 1}ᶜ := by ext h; simp; omega
  rw [RRT.replicate_heightLaw, hcomp, measureReal_compl (by trivial),
    measureReal_compl (by trivial), probReal_univ, probReal_univ] at htail
  have hr : (Forward.heightLaw RRT.allAttach n).real {h | h ≤ 1} =
      (1 : ℝ) / (Nat.factorial n : ℝ) := by
    rw [Measure.real, RRT.height_le_one_mass]
    simp
  have ha : (alternatingWord n).heightLaw.real {h | h ≤ 1} =
      (1 : ℝ) / (2 ^ (n - 1) : ℕ) := by
    rw [Measure.real, height_le_one_mass_of_pos (by omega : 1 ≤ n)]
    simp
  rw [hr, ha] at htail
  have hc := inv_factorial_lt_inv_two_pow_pred hn
  linarith

end Alternating
end FreezingGrowth
