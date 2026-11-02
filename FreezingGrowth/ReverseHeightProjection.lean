module

public import FreezingGrowth.ReverseComponentHeight
public import FreezingGrowth.ReverseHeightList
public import Mathlib.Data.List.InsertIdx

/-!
# Exact projection from ordered forests to component heights

The deterministic graft on the actual forest projects to the list operation
used by the height coupling. In particular, the receiver and donor are the
stored list entries at the sampled indices, and deleting the donor preserves
the order of every surviving component.
-/

@[expose] public section

namespace FreezingGrowth.ReverseOrdered

open scoped Classical

theorem heightProfile_getD (F : Forest) (i : Fin F.rootOrder.length) :
    (heightProfile F)[i.val]?.getD 0 = F.forest.componentHeight (F.rootOrder.get i) := by
  simp [heightProfile]

/-- Every actual ordered graft has exactly the height-list update of
Algorithm 3. No probabilistic equivalence is assumed here. -/
theorem heightProfile_joinChoice (F : Forest) (a b : Fin F.rootOrder.length)
    (hab : a ≠ b) :
    heightProfile (joinChoice F (F.rootOrder.get a, F.rootOrder.get b)) =
      ReverseHeightList.graft (heightProfile F) a.val b.val := by
  let : BEq (ℕ ⊕ ℕ) := instBEqOfDecidableEq
  let : LawfulBEq (ℕ ⊕ ℕ) := by infer_instance
  let ra := F.rootOrder.get a
  let rb := F.rootOrder.get b
  have hra : ra ∈ F.forest.roots := (mem_rootOrder F _).mp (List.get_mem _ _)
  have hrb : rb ∈ F.forest.roots := (mem_rootOrder F _).mp (List.get_mem _ _)
  have hrab : ra ≠ rb := fun h => hab (F.rootOrder_nodup.injective_get h)
  have hp : (ra, rb) ∈ F.forest.roots.offDiag :=
    Finset.mem_offDiag.mpr ⟨hra, hrb, hrab⟩
  let hnew := max (F.forest.componentHeight ra) (F.forest.componentHeight rb + 1)
  have hfilter : F.rootOrder.filter (fun r => decide (r ≠ rb)) =
      F.rootOrder.eraseIdx b.val := by
    calc
      _ = F.rootOrder.erase rb := by
        rw [F.rootOrder_nodup.erase_eq_filter]
        congr 1
      _ = _ := F.rootOrder_nodup.erase_get b
  have hprofile :
      heightProfile (joinChoice F (ra, rb)) =
        (F.rootOrder.filter (fun r => decide (r ≠ rb))).map
          (Function.update F.forest.componentHeight ra hnew) := by
    unfold heightProfile
    rw [joinChoice_rootOrder F hp]
    apply List.map_congr_left
    intro r hr
    have hr' := List.mem_filter.mp hr
    have hrb' : r ≠ rb := of_decide_eq_true hr'.2
    rw [joinChoice_forest]
    simp only [RootedForest.joinChoice, dite_eq_left hp]
    by_cases hra' : r = ra
    · subst r
      simpa [hnew] using F.forest.componentHeight_join_receiver hra hrb hrab
    · rw [F.forest.componentHeight_join_other hra hrb hrab hra' hrb']
      simp [Function.update_of_ne hra']
  have hupdate : F.rootOrder.map (Function.update F.forest.componentHeight ra hnew) =
      (heightProfile F).set a.val hnew := by
    rw [F.rootOrder_nodup.map_update, ite_eq_left (List.get_mem _ _)]
    change (F.rootOrder.map F.forest.componentHeight).set
      (F.rootOrder.idxOf (F.rootOrder.get a)) hnew = _
    simpa [heightProfile] using congrArg
      (fun i => (F.rootOrder.map F.forest.componentHeight).set i hnew)
      (F.rootOrder_nodup.idxOf_getElem a.val a.isLt)
  change heightProfile (joinChoice F (ra, rb)) = _
  rw [hprofile, hfilter, ← List.eraseIdx_map, hupdate]
  simp only [ReverseHeightList.graft, heightProfile_getD, ra, rb, hnew]

end FreezingGrowth.ReverseOrdered
