module

public import FreezingGrowth.MainStatements
public import FreezingGrowth.ChoiceSequence

/-! Birth-ordered selectors for the two active vertices at a seed prefix. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

noncomputable def birthOrderedFirstSeed (s : Forward.State) : ℕ :=
  if h : s.active.Nonempty then s.active.min' h else 0

noncomputable def birthOrderedSecondSeed (s : Forward.State) : ℕ :=
  if h : s.active.Nonempty then s.active.max' h else 0

theorem birthOrderedSeed_spec (s : Forward.State) (hcard : s.active.card = 2) :
    s.active = {birthOrderedFirstSeed s, birthOrderedSecondSeed s} ∧
      birthOrderedFirstSeed s < birthOrderedSecondSeed s := by
  have hne : s.active.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hfirst : birthOrderedFirstSeed s = s.active.min' hne := by
    simp [birthOrderedFirstSeed, hne]
  have hsecond : birthOrderedSecondSeed s = s.active.max' hne := by
    simp [birthOrderedSecondSeed, hne]
  have hlt : birthOrderedFirstSeed s < birthOrderedSecondSeed s := by
    rw [hfirst, hsecond]
    apply Finset.min'_lt_max'_of_card
    omega
  have hfirst_mem : birthOrderedFirstSeed s ∈ s.active := by
    rw [hfirst]
    exact Finset.min'_mem _ _
  have hsecond_mem : birthOrderedSecondSeed s ∈ s.active := by
    rw [hsecond]
    exact Finset.max'_mem _ _
  have hsubset :
      ({birthOrderedFirstSeed s, birthOrderedSecondSeed s} : Finset ℕ) ⊆ s.active := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hfirst_mem
    · exact hsecond_mem
  have hpair_card :
      ({birthOrderedFirstSeed s, birthOrderedSecondSeed s} : Finset ℕ).card = 2 := by
    simp [ne_of_lt hlt]
  have hset :
      ({birthOrderedFirstSeed s, birthOrderedSecondSeed s} : Finset ℕ) = s.active :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hpair_card, hcard])
  exact ⟨hset.symm, hlt⟩

private theorem attachAttachFreeze_admissible :
    Word.admissible [true, true, false] := by
  intro j hj
  have hj' : j < 3 := by simpa using hj
  interval_cases j <;> norm_num [Word.toSigns, activeCount, Finset.sum_range_succ]

private theorem attachFreezeAttach_admissible :
    Word.admissible [true, false, true] := by
  intro j hj
  have hj' : j < 3 := by simpa using hj
  interval_cases j <;> norm_num [Word.toSigns, activeCount, Finset.sum_range_succ]

private theorem attachAttachFreeze_activeCount :
    activeCount (Word.toSigns [true, true, false]) 3 = 2 := by
  norm_num [Word.toSigns, activeCount, Finset.sum_range_succ]

private theorem attachFreezeAttach_activeCount :
    activeCount (Word.toSigns [true, false, true]) 3 = 2 := by
  norm_num [Word.toSigns, activeCount, Finset.sum_range_succ]

theorem attachAttachFreeze_active_card :
    ∀ᵐ s ∂Forward.treeLaw (Word.toSigns [true, true, false]) 3,
      s.active.card = 2 := by
  have hτ : (3 : ℕ∞) ≤ extinctionTime (Word.toSigns [true, true, false]) :=
    (Word.admissible_iff_le_extinctionTime [true, true, false]).mp
      attachAttachFreeze_admissible
  have hc := Forward.treeLaw_counts (Word.toSigns [true, true, false]) 3 hτ
  filter_upwards [hc] with s hs
  have hcard : (s.active.card : ℤ) = 2 := by
    rw [hs.1, attachAttachFreeze_activeCount]
  omega

theorem attachFreezeAttach_active_card :
    ∀ᵐ s ∂Forward.treeLaw (Word.toSigns [true, false, true]) 3,
      s.active.card = 2 := by
  have hτ : (3 : ℕ∞) ≤ extinctionTime (Word.toSigns [true, false, true]) :=
    (Word.admissible_iff_le_extinctionTime [true, false, true]).mp
      attachFreezeAttach_admissible
  have hc := Forward.treeLaw_counts (Word.toSigns [true, false, true]) 3 hτ
  filter_upwards [hc] with s hs
  have hcard : (s.active.card : ℤ) = 2 := by
    rw [hs.1, attachFreezeAttach_activeCount]
  omega

end FreezingGrowth.TwoSeedGraft
