module

public import FreezingGrowth.ReverseForest
public import FreezingGrowth.ReverseIndexedKernel
public import Mathlib.Data.List.Nodup

/-!
# The ordered forest process of Algorithm 2

The component list is represented by its root order together with the complete
rooted forest. Grafting the second selected component under the first removes
only the second root from the list, preserving every other relative position.
Undoing a freeze appends its singleton at the end. Forgetting this order gives
exactly the graph-valued reverse law at every phase, including extinction.
-/

@[expose] public section

namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical ENNReal

/-- A concrete component list with no omitted or repeated components. -/
structure Forest where
  forest : Reverse.Forest
  rootOrder : List (ℕ ⊕ ℕ)
  rootOrder_nodup : rootOrder.Nodup
  rootOrder_roots : rootOrder.toFinset = forest.roots

instance : MeasurableSpace Forest := ⊤
instance : DiscreteMeasurableSpace Forest := ⟨fun _ => trivial⟩

theorem rootOrder_length (F : Forest) : F.rootOrder.length = F.forest.roots.card := by
  rw [← F.rootOrder_roots, List.toFinset_card_of_nodup F.rootOrder_nodup]

theorem mem_rootOrder (F : Forest) (v : ℕ ⊕ ℕ) :
    v ∈ F.rootOrder ↔ v ∈ F.forest.roots := by
  rw [← F.rootOrder_roots]
  exact List.mem_toFinset.symm

/-- The exact enumeration carried by the stored component list. -/
noncomputable def rootEnumeration (F : Forest) : F.forest.RootEnumeration :=
  Equiv.ofBijective
    (fun i => ⟨F.rootOrder.get ⟨i.val, by rw [rootOrder_length]; exact i.isLt⟩,
      (mem_rootOrder F _).mp (List.get_mem _ _)⟩)
    (by
      constructor
      · intro i j he
        apply Fin.ext
        exact congrArg (fun k : Fin F.rootOrder.length => k.val)
          (F.rootOrder_nodup.injective_get (congrArg Subtype.val he))
      · intro r
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((mem_rootOrder F _).mpr r.property)
        refine ⟨⟨j.val, by rw [← rootOrder_length]; exact j.isLt⟩, Subtype.ext ?_⟩
        simpa using hj)

/-- List position `i` denotes precisely its stored `get` entry. -/
theorem rootEnumeration_get (F : Forest) (i : Fin F.forest.roots.card) :
    (rootEnumeration F i).val =
      F.rootOrder.get ⟨i.val, by rw [rootOrder_length]; exact i.isLt⟩ := rfl

/-- Any fixed initial enumeration is permitted: the active singletons have
identical displayed labels, and the kernel is enumeration independent. -/
noncomputable def initial (x : SignSequence) (n : ℕ) : Forest where
  forest := Reverse.initial x n
  rootOrder := (Reverse.initial x n).roots.toList
  rootOrder_nodup := Finset.nodup_toList _
  rootOrder_roots := Finset.toList_toFinset _

/-- Preserve the receiver's position and delete the grafted component's root. -/
def joinChoice (F : Forest) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) : Forest :=
  if hp : p ∈ F.forest.roots.offDiag then
    { forest := F.forest.join p.1 p.2 (Finset.mem_offDiag.mp hp).1
        (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2
      rootOrder := F.rootOrder.filter (fun r => decide (r ≠ p.2))
      rootOrder_nodup := F.rootOrder_nodup.filter _
      rootOrder_roots := by
        rw [RootedForest.join_roots]
        ext r
        simp [mem_rootOrder F, and_comm] }
  else F

theorem joinChoice_forest (F : Forest) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) :
    (joinChoice F p).forest = F.forest.joinChoice p := by
  unfold joinChoice RootedForest.joinChoice
  split_ifs <;> rfl

theorem joinChoice_rootOrder (F : Forest) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    (joinChoice F p).rootOrder = F.rootOrder.filter (fun r => decide (r ≠ p.2)) := by
  simp [joinChoice, hp]

/-- Append the fresh frozen singleton, exactly as required by Algorithm 2. -/
def insertLabel (F : Forest) (i : ℕ) : Forest :=
  if h : Sum.inr i ∈ F.forest.vertices then F else
    { forest := F.forest.adjoin (.inr i) h
      rootOrder := F.rootOrder ++ [.inr i]
      rootOrder_nodup := by
        have hn : Sum.inr i ∉ F.rootOrder := by
          intro hv
          exact h (RootedForest.mem_roots.mp ((mem_rootOrder F _).mp hv)).1
        exact F.rootOrder_nodup.append (by simp) (by simpa using hn)
      rootOrder_roots := by
        rw [RootedForest.adjoin_roots]
        simp [F.rootOrder_roots] }

theorem insertLabel_forest (F : Forest) (i : ℕ) :
    (insertLabel F i).forest = Reverse.insertLabel F.forest i := by
  unfold insertLabel Reverse.insertLabel
  split_ifs <;> rfl

theorem insertLabel_rootOrder (F : Forest) {i : ℕ}
    (hfresh : Sum.inr i ∉ F.forest.vertices) :
    (insertLabel F i).rootOrder = F.rootOrder ++ [.inr i] := by
  simp [insertLabel, hfresh]

/-- The actual ordered grafting kernel. Root labels are just the bijective
coordinates of the uniformly chosen list positions. -/
noncomputable def joinLaw (F : Forest) : Measure Forest :=
  if 2 ≤ F.forest.roots.card then
    (uniformRootPair F.forest.roots).map (joinChoice F)
  else Measure.dirac F

instance joinLaw_probability (F : Forest) : IsProbabilityMeasure (joinLaw F) := by
  unfold joinLaw
  split_ifs with h
  · have := uniformRootPair_isProbabilityMeasure F.forest.roots h
    exact (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr
      inferInstance
  · infer_instance

/-- The index-sampling description is equivalent for every root enumeration. -/
theorem joinLaw_eq_indexed (F : Forest) (e : F.forest.RootEnumeration)
    (hF : 2 ≤ F.forest.roots.card) :
    joinLaw F =
      (uniformRootPair (Finset.univ : Finset (Fin F.forest.roots.card))).map
        (fun p => joinChoice F (F.forest.indexedPair e p)) := by
  rw [joinLaw, ite_eq_left hF,
    ← F.forest.map_uniformRootPair_indexedPair e,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- Specializing to the stored list gives the literal list-index operation
of Algorithm 2; `rootEnumeration_get` identifies each selected entry. -/
theorem joinLaw_eq_list_indices (F : Forest) (hF : 2 ≤ F.forest.roots.card) :
    joinLaw F =
      (uniformRootPair (Finset.univ : Finset (Fin F.forest.roots.card))).map
        (fun p => joinChoice F (F.forest.indexedPair (rootEnumeration F) p)) :=
  joinLaw_eq_indexed F (rootEnumeration F) hF

/-- Forgetting the component order gives exactly the existing graph kernel. -/
theorem map_joinLaw (F : Forest) :
    (joinLaw F).map Forest.forest = F.forest.joinLaw := by
  unfold joinLaw RootedForest.joinLaw
  split_ifs
  · rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    congr 1
    funext p
    exact joinChoice_forest F p
  · exact Measure.map_dirac' measurable_from_top _

noncomputable def transitionLaw (x : SignSequence) (i : ℕ) (F : Forest) : Measure Forest :=
  if x (i + 1) then joinLaw F else Measure.dirac (insertLabel F i)

instance transitionLaw_probability (x : SignSequence) (i : ℕ) (F : Forest) :
    IsProbabilityMeasure (transitionLaw x i F) := by
  unfold transitionLaw
  split_ifs <;> infer_instance

theorem map_transitionLaw (x : SignSequence) (i : ℕ) (F : Forest) :
    (transitionLaw x i F).map Forest.forest = Reverse.transitionLaw x i F.forest := by
  by_cases hx : x (i + 1) = true
  · rw [transitionLaw, Reverse.transitionLaw, ite_eq_left hx, ite_eq_left hx]
    exact map_joinLaw F
  · rw [transitionLaw, Reverse.transitionLaw, ite_eq_right hx, ite_eq_right hx,
      Measure.map_dirac' measurable_from_top, insertLabel_forest]

/-- The entire backwards ordered construction, held fixed after its horizon. -/
noncomputable def lawAfter (x : SignSequence) (n : ℕ) : ℕ → Measure Forest
  | 0 => Measure.dirac (initial x n)
  | k + 1 => if k < n then
      (lawAfter x n k).bind (transitionLaw x (n - (k + 1)))
    else lawAfter x n k

instance lawAfter_probability (x : SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (lawAfter x n k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac (initial x n)); infer_instance
  | succ k ih =>
    simp only [lawAfter]
    split_ifs
    · exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
        (Filter.Eventually.of_forall (fun F => transitionLaw_probability x _ F))
    · exact ih

/-- The source ordered construction projects to the graph-valued construction
at every phase, for every horizon, including the empty initialization. -/
theorem map_lawAfter (x : SignSequence) (n k : ℕ) :
    (lawAfter x n k).map Forest.forest = Reverse.lawAfter x n k := by
  induction k with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ k ih =>
    simp only [lawAfter, Reverse.lawAfter]
    split_ifs
    · rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      calc
        _ = (lawAfter x n k).bind
            (fun F => Reverse.transitionLaw x (n - (k + 1)) F.forest) := by
          congr 1
          funext F
          exact map_transitionLaw x (n - (k + 1)) F
        _ = ((lawAfter x n k).map Forest.forest).bind
            (Reverse.transitionLaw x (n - (k + 1))) :=
          (Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
        _ = _ := by rw [ih]
    · exact ih

/-- Correct components and acyclicity hold in every sampled ordered forest. -/
theorem lawAfter_valid (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ F ∂lawAfter x n k, Reverse.ValidAt x n (n - k) F.forest := by
  have h := Reverse.lawAfter_valid x n k hn hk
  rw [← map_lawAfter x n k] at h
  exact (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mp h

/-- The list has exactly the population specified by the source walk. -/
theorem lawAfter_rootOrder_length (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ F ∂lawAfter x n k, F.rootOrder.length = (activeCount x (n - k)).toNat := by
  filter_upwards [lawAfter_valid x n k hn hk] with F hF
  exact (rootOrder_length F).trans hF.roots_card

/-- Every legal attachment has two different component roots available;
the identity totalization of the indexed kernel is never used there. -/
theorem valid_attachment_two_roots {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F.forest) (hx : x (i + 1) = true) :
    2 ≤ F.forest.roots.card := by
  rw [hF.roots_card]
  apply two_le_activeCount_toNat_succ_of_attachment _ hx
  exact le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn

/-- The prescribed singleton is always fresh at its legal reverse phase. -/
theorem valid_freezing_fresh {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : Reverse.ValidAt x n (i + 1) F.forest) :
    Sum.inr i ∉ F.forest.vertices := by
  rw [hF.vertices_eq]
  exact Reverse.fresh_freezing_label x n i

noncomputable def treeLaw (x : SignSequence) (n : ℕ) : Measure Forest := lawAfter x n n

instance treeLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (treeLaw x n) := lawAfter_probability x n n

theorem map_treeLaw (x : SignSequence) (n : ℕ) :
    (treeLaw x n).map Forest.forest = Reverse.treeLaw x n := map_lawAfter x n n

end FreezingGrowth.ReverseOrdered
