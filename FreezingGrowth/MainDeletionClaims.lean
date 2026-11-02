module

public import FreezingGrowth.FreezeAttachGap
public import FreezingGrowth.AttachFreezeGap
public import FreezingGrowth.TwoSurvivorAdmissible
public import FreezingGrowth.HeightExpectationOrder

/-! The first two assertions of Proposition 1.1, using the same witnesses
required by each source target and actual finite-word expected heights. -/

@[expose] public section
namespace FreezingGrowth

theorem removeFreezeAttachClaim : RemoveFreezeAttachClaim := by
  intro A _hA
  obtain ⟨m, hm, hgap⟩ := exists_freezeAttachExpectedGap_ge A
  have hm1 : 1 ≤ m := by omega
  have hgain :
      Word.expectedHeight ((twoActivePrefix m ++ [false, true]) ++ List.replicate (m ^ 9) true) + A ≤
        Word.expectedHeight (twoActivePrefix m ++ List.replicate (m ^ 9) true) := by
    unfold freezeAttachExpectedGap at hgap
    linarith
  have hmono : Word.expectedHeight (twoActivePrefix m ++ List.replicate (m ^ 9) true) ≤
      Word.expectedHeight (twoActivePrefix m ++ List.replicate (m ^ 9 + 1) true) := by
    simpa only [List.replicate_succ', List.append_assoc] using
      Word.expectedHeight_le_append (twoActivePrefix m ++ List.replicate (m ^ 9) true) [true]
  refine ⟨m, m ^ 9, ?_⟩
  dsimp only
  refine ⟨hm1, ?_, twoActivePrefix_grow_admissible m hm1 (m ^ 9),
    twoActivePrefix_grow_admissible m hm1 (m ^ 9 + 1), ?_, ?_⟩
  · simpa only [List.append_assoc] using twoActivePrefix_freeze_attach_admissible m hm1 (m ^ 9)
  · simpa only [List.append_assoc] using hgain
  · simpa only [List.append_assoc] using hgain.trans hmono

theorem removeAttachFreezeClaim : RemoveAttachFreezeClaim := by
  intro A _hA
  obtain ⟨m, hm, hgap⟩ := exists_freezeAttachExpectedGap_ge (3 * A + 2)
  have hm1 : 1 ≤ m := by omega
  have hcompare := attachFreeze_expected_gap_ge m hm1 (m ^ 9)
  have hgain :
      Word.expectedHeight ((twoActivePrefix m ++ [true, false]) ++ List.replicate (m ^ 9) true) + A ≤
        Word.expectedHeight (twoActivePrefix m ++ List.replicate (m ^ 9) true) := by
    unfold freezeAttachExpectedGap at hgap
    linarith
  refine ⟨m, m ^ 9, ?_⟩
  dsimp only
  refine ⟨hm1, ?_, twoActivePrefix_grow_admissible m hm1 (m ^ 9), ?_⟩
  · simpa only [List.append_assoc] using twoActivePrefix_attach_freeze_admissible m hm1 (m ^ 9)
  · simpa only [List.append_assoc] using hgain

end FreezingGrowth
