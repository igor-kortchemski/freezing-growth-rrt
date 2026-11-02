module

public import FreezingGrowth.ReverseDistinguishedInitialization

/-! Arbitrary component ordering preserves the complete labelled-forest law.
The ordering chosen after a graft may depend on the selected ordered pair.
Uniform sampling and the underlying graph operation are retained exactly. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical ENNReal

/-- Change only the component order; the complete rooted forest is fixed. -/
structure Reordering where
  apply : Forest → Forest
  forest_eq : ∀ F, (apply F).forest = F.forest

def Reordering.identity : Reordering := ⟨id, fun _ => rfl⟩

/-- Every permutation of the entire root list gives a genuine reordering. -/
def reorderAs (F : Forest) (order : List Label) (h : order.Perm F.rootOrder) : Forest where
  forest := F.forest
  rootOrder := order
  rootOrder_nodup := h.nodup_iff.mpr F.rootOrder_nodup
  rootOrder_roots := (List.toFinset_eq_of_perm _ _ h).trans F.rootOrder_roots

def Reordering.ofPerm (order : Forest → List Label)
    (h : ∀ F, (order F).Perm F.rootOrder) : Reordering :=
  ⟨fun F => reorderAs F (order F) (h F), fun _ => rfl⟩

/-- A policy chooses component order only. Its graft ordering may depend on
the preceding ordered forest, time, and fresh selected root pair. -/
structure OrderingPolicy where
  initial : Reordering
  graft : ℕ → Forest → Label × Label → Forest
  graft_forest : ∀ i F p, (graft i F p).forest = F.forest.joinChoice p
  singleton : ℕ → Forest → Forest
  singleton_forest : ∀ i F, (singleton i F).forest = Reverse.insertLabel F.forest i

/-- The source's original append-singleton, receiver-position convention. -/
def OrderingPolicy.standard : OrderingPolicy where
  initial := Reordering.identity
  graft _ := joinChoice
  graft_forest _ := joinChoice_forest
  singleton i F := insertLabel F i
  singleton_forest i F := insertLabel_forest F i

/-- Independent root-list permutation choices after every operation, with
the fresh graft pair explicitly available to the ordering policy. -/
def OrderingPolicy.ofReorderings (initial : Reordering)
    (afterGraft : ℕ → Forest → Label × Label → Reordering)
    (afterSingleton : ℕ → Forest → Reordering) : OrderingPolicy where
  initial := initial
  graft i F p := (afterGraft i F p).apply (joinChoice F p)
  graft_forest i F p := ((afterGraft i F p).forest_eq _).trans (joinChoice_forest F p)
  singleton i F := (afterSingleton i F).apply (insertLabel F i)
  singleton_forest i F := ((afterSingleton i F).forest_eq _).trans (insertLabel_forest F i)

/-- The specific front-singleton and distinguished-receiver order changes
used locally by Algorithm 3 are actual instances of the general policy. -/
def OrderingPolicy.distinguished (d : Label) : OrderingPolicy where
  initial := Reordering.identity
  graft _ F p := distinguishedJoinChoice F d p
  graft_forest _ F p := distinguishedJoinChoice_forest F d p
  singleton i F := prependLabel F i
  singleton_forest i F := prependLabel_forest F i

noncomputable def joinLawWithOrdering (P : OrderingPolicy) (i : ℕ) (F : Forest) : Measure Forest :=
  if 2 ≤ F.forest.roots.card then
    (uniformRootPair F.forest.roots).map (P.graft i F)
  else Measure.dirac F

instance joinLawWithOrdering_probability (P : OrderingPolicy) (i : ℕ) (F : Forest) :
    IsProbabilityMeasure (joinLawWithOrdering P i F) := by
  unfold joinLawWithOrdering
  split_ifs with h
  · let := uniformRootPair_isProbabilityMeasure F.forest.roots h
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr
      inferInstance
  · infer_instance

theorem map_joinLawWithOrdering (P : OrderingPolicy) (i : ℕ) (F : Forest) :
    (joinLawWithOrdering P i F).map Forest.forest = F.forest.joinLaw := by
  unfold joinLawWithOrdering RootedForest.joinLaw
  split_ifs
  · rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    congr 1
    funext p
    exact P.graft_forest i F p
  · exact Measure.map_dirac' measurable_from_top _

noncomputable def transitionLawWithOrdering (P : OrderingPolicy) (x : SignSequence)
    (i : ℕ) (F : Forest) : Measure Forest :=
  if x (i + 1) then joinLawWithOrdering P i F else Measure.dirac (P.singleton i F)

instance transitionLawWithOrdering_probability (P : OrderingPolicy) (x : SignSequence)
    (i : ℕ) (F : Forest) : IsProbabilityMeasure (transitionLawWithOrdering P x i F) := by
  unfold transitionLawWithOrdering
  split_ifs <;> infer_instance

theorem map_transitionLawWithOrdering (P : OrderingPolicy) (x : SignSequence)
    (i : ℕ) (F : Forest) :
    (transitionLawWithOrdering P x i F).map Forest.forest =
      Reverse.transitionLaw x i F.forest := by
  by_cases hx : x (i + 1) = true
  · rw [transitionLawWithOrdering, Reverse.transitionLaw, ite_eq_left hx, ite_eq_left hx]
    exact map_joinLawWithOrdering P i F
  · rw [transitionLawWithOrdering, Reverse.transitionLaw, ite_eq_right hx, ite_eq_right hx,
      Measure.map_dirac' measurable_from_top, P.singleton_forest]

noncomputable def lawAfterWithOrdering (P : OrderingPolicy) (x : SignSequence) (n : ℕ) :
    ℕ → Measure Forest
  | 0 => Measure.dirac (P.initial.apply (initial x n))
  | k + 1 => if k < n then
      (lawAfterWithOrdering P x n k).bind (transitionLawWithOrdering P x (n - (k + 1)))
    else lawAfterWithOrdering P x n k

instance lawAfterWithOrdering_probability (P : OrderingPolicy) (x : SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (lawAfterWithOrdering P x n k) := by
  induction k with
  | zero =>
    change IsProbabilityMeasure (Measure.dirac (P.initial.apply (initial x n)))
    infer_instance
  | succ k ih =>
    simp only [lawAfterWithOrdering]
    split_ifs
    · exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
        (Filter.Eventually.of_forall (fun F => transitionLawWithOrdering_probability P x _ F))
    · exact ih

/-- At every reverse phase, arbitrary permitted order choices have exactly
the original full rooted, vertex-labelled forest law. Extinction is included. -/
theorem map_lawAfterWithOrdering (P : OrderingPolicy) (x : SignSequence) (n k : ℕ) :
    (lawAfterWithOrdering P x n k).map Forest.forest = Reverse.lawAfter x n k := by
  induction k with
  | zero =>
    change (Measure.dirac _).map Forest.forest = Measure.dirac _
    rw [Measure.map_dirac' measurable_from_top, P.initial.forest_eq]
    rfl
  | succ k ih =>
    simp only [lawAfterWithOrdering, Reverse.lawAfter]
    split_ifs
    · rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      calc
        _ = (lawAfterWithOrdering P x n k).bind
            (fun F => Reverse.transitionLaw x (n - (k + 1)) F.forest) := by
          congr 1
          funext F
          exact map_transitionLawWithOrdering P x (n - (k + 1)) F
        _ = ((lawAfterWithOrdering P x n k).map Forest.forest).bind
            (Reverse.transitionLaw x (n - (k + 1))) :=
          (Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
        _ = _ := by rw [ih]
    · exact ih

theorem lawAfter_order_independent (P Q : OrderingPolicy) (x : SignSequence) (n k : ℕ) :
    (lawAfterWithOrdering P x n k).map Forest.forest =
      (lawAfterWithOrdering Q x n k).map Forest.forest := by
  rw [map_lawAfterWithOrdering, map_lawAfterWithOrdering]

/-- In particular, the complete terminal labelled-tree law is unchanged. -/
theorem treeLaw_order_independent (P : OrderingPolicy) (x : SignSequence) (n : ℕ) :
    (lawAfterWithOrdering P x n n).map Forest.forest = Reverse.treeLaw x n :=
  map_lawAfterWithOrdering P x n n

end FreezingGrowth.ReverseOrdered
