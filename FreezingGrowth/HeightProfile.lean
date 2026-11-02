module

public import FreezingGrowth.Height

/-!
# The finite height profile of the forward tree

The profile retains the multiset of active depths and the maximum depth over
all vertices, including frozen vertices. Uniform choice from the multiset
counts repeated depths with their multiplicities. Its transition law is the
pushforward of Algorithm 1, and its maximum therefore has the genuine tree
height law.

This supplies a mathematical soundness bridge for finite profile computation.
It does not itself implement or certify a rational enumeration.
-/

@[expose] public section

namespace FreezingGrowth

/-- Information needed to evolve the height law, including frozen maxima. -/
@[ext]
structure HeightProfile where
  activeDepths : Multiset ℕ
  maximum : ℕ
  deriving DecidableEq

namespace HeightProfile

open MeasureTheory
open scoped ENNReal Classical

instance : MeasurableSpace HeightProfile := ⊤
instance : DiscreteMeasurableSpace HeightProfile := ⟨fun _ => trivial⟩

/-- Forget vertex labels and edges while retaining active-depth multiplicities. -/
def ofState (s : Forward.State) : HeightProfile :=
  ⟨s.active.val.map s.height, Forward.treeHeight s⟩

def initial : HeightProfile := ⟨{0}, 0⟩

/-- The parent stays active and a new child is added one level below it. -/
def attach (p : HeightProfile) (d : ℕ) : HeightProfile :=
  ⟨(d + 1) ::ₘ p.activeDepths, max p.maximum (d + 1)⟩

/-- Freezing removes one active occurrence, without removing any vertex. -/
def freeze (p : HeightProfile) (d : ℕ) : HeightProfile :=
  ⟨p.activeDepths.erase d, p.maximum⟩

def step (p : HeightProfile) (sign : Bool) (d : ℕ) : HeightProfile :=
  if sign then attach p d else freeze p d

@[simp]
theorem activeDepths_card_ofState (s : Forward.State) :
    (ofState s).activeDepths.card = s.active.card := by
  simp [ofState]

theorem activeDepths_eq_zero_iff (s : Forward.State) :
    (ofState s).activeDepths = 0 ↔ s.active = ∅ := by
  constructor
  · intro h
    apply Finset.card_eq_zero.mp
    have hc := congrArg Multiset.card h
    simpa using hc
  · intro h
    simp [ofState, h]

@[simp]
theorem ofState_initial : ofState Forward.initial = initial := by
  ext <;> simp [ofState, initial, Forward.initial, Forward.treeHeight]

theorem ofState_freeze (s : Forward.State) (t : ℕ) {v : ℕ}
    (hv : v ∈ s.active) :
    ofState (Forward.freeze s t v) = freeze (ofState s) (s.height v) := by
  apply HeightProfile.ext
  · change (s.active.erase v).val.map s.height =
      (s.active.val.map s.height).erase (s.height v)
    rw [Finset.erase_val]
    exact Multiset.map_erase_of_mem s.height s.active.val hv
  · rfl

theorem ofState_attach {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s)
    (v : ℕ) :
    ofState (Forward.attach s (n + 1) v) = attach (ofState s) (s.height v) := by
  have ht : n + 1 ∉ s.vertices := by
    intro h
    have := hs.vertices_le _ h
    omega
  have ha : n + 1 ∉ s.active := fun h => ht (hs.active_subset h)
  apply HeightProfile.ext
  · change (insert (n + 1) s.active).val.map
        (Function.update s.height (n + 1) (s.height v + 1)) =
      (s.height v + 1) ::ₘ s.active.val.map s.height
    rw [Finset.insert_val_of_notMem ha, Multiset.map_cons, Function.update_self]
    congr 1
    apply Multiset.map_congr rfl
    intro w hw
    have hwne : w ≠ n + 1 := fun h => ha (h ▸ hw)
    simp [hwne]
  · exact Forward.treeHeight_attach s (n + 1) v ht

theorem ofState_step {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s)
    {v : ℕ} (hv : v ∈ s.active) (sign : Bool) :
    ofState (Forward.step s (n + 1) sign v) = step (ofState s) sign (s.height v) := by
  cases sign
  · simpa [Forward.step, step, hv] using ofState_freeze s (n + 1) hv
  · simpa [Forward.step, step, hv] using ofState_attach hs v

/-- Uniform vertices project to depths with multiplicity, including coincident depths. -/
theorem map_uniform_activeDepths (s : Forward.State) :
    (Measure.uniformOfFinset s.active).map s.height =
      Measure.ofMultiset (ofState s).activeDepths := by
  apply Measure.ext_of_singleton
  intro d
  rw [Measure.map_apply measurable_from_top (measurableSet_singleton d),
    Measure.uniformOfFinset_apply, Measure.ofMultiset_apply_singleton]
  have hc : (s.active.filter (fun v => s.height v = d)).card =
      (s.active.val.map s.height).count d := by
    rw [Multiset.count_map]
    change (s.active.filter (fun v => s.height v = d)).val.card = _
    rw [Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro v _
    exact eq_comm
  simp only [ofState, Multiset.card_map, Finset.card_val, Set.mem_preimage,
    Set.mem_singleton_iff, hc]
  exact congrArg (fun dec : DecidableEq ℕ =>
    (@Multiset.count ℕ dec d (s.active.val.map s.height) : ℝ≥0∞) / s.active.card)
    (Subsingleton.elim _ _)

/-- Depth dynamics: choose an active occurrence uniformly, or absorb after extinction. -/
noncomputable def transitionLaw (p : HeightProfile) (sign : Bool) : Measure HeightProfile :=
  if p.activeDepths = 0 then Measure.dirac p
  else (Measure.ofMultiset p.activeDepths).map (step p sign)

/-- One step of the full state law has exactly the profile transition law. -/
theorem map_transitionLaw {n : ℕ} {s : Forward.State} (hs : Forward.ValidAt n s)
    (sign : Bool) :
    (Forward.transitionLaw s (n + 1) sign).map ofState =
      transitionLaw (ofState s) sign := by
  by_cases ha : s.active.Nonempty
  · have hp : (ofState s).activeDepths ≠ 0 := by
      intro h
      exact ha.ne_empty ((activeDepths_eq_zero_iff s).mp h)
    have hu : ∀ᵐ v ∂Measure.uniformOfFinset s.active, v ∈ s.active := by
      rw [ae_iff, Measure.uniformOfFinset_apply]
      simp
    rw [Forward.transitionLaw, ite_eq_left ha, transitionLaw, ite_eq_right hp,
      Measure.map_map measurable_from_top measurable_from_top,
      ← map_uniform_activeDepths s,
      Measure.map_map measurable_from_top measurable_from_top]
    apply Measure.map_congr
    filter_upwards [hu] with v hv
    exact ofState_step hs hv sign
  · have he : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    rw [Forward.transitionLaw_eq_dirac_of_empty s (n + 1) sign he,
      Measure.map_dirac, transitionLaw, ite_eq_left ((activeDepths_eq_zero_iff s).mpr he)]

/-- Profile distribution after a prescribed finite number of signs. -/
noncomputable def law (x : SignSequence) : ℕ → Measure HeightProfile
  | 0 => Measure.dirac initial
  | n + 1 => (law x n).bind (fun p => transitionLaw p (x (n + 1)))

/-- The profile dynamics characterize the actual forward tree projection. -/
theorem map_treeLaw (x : SignSequence) (n : ℕ) :
    (Forward.treeLaw x n).map ofState = law x n := by
  induction n with
  | zero => simp [Forward.treeLaw, law]
  | succ n ih =>
    rw [Forward.treeLaw,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      law, ← ih,
      Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [Forward.treeLaw_valid x n] with s hs
    exact map_transitionLaw hs (x (n + 1))

instance law_probability (x : SignSequence) (n : ℕ) : IsProbabilityMeasure (law x n) := by
  rw [← map_treeLaw]
  exact (Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable).mpr
    inferInstance

/-- Computing the stored maximum gives exactly the height distribution in the paper model. -/
theorem map_law_maximum (x : SignSequence) (n : ℕ) :
    (law x n).map HeightProfile.maximum = Forward.heightLaw x n := by
  rw [← map_treeLaw, Measure.map_map measurable_from_top measurable_from_top]
  rfl

end HeightProfile

end FreezingGrowth
