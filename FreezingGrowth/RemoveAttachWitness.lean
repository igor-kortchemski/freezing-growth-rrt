module

public import FreezingGrowth.ProfileEnumeration
public import FreezingGrowth.MainStatements

/-!
# The finite words used for the attachment-removal counterexample

The two concrete schedules and the arithmetic implication of exact integer
statistics are separated from the numerical certificates. No numerical
computation is assumed as a mathematical axiom.
-/

@[expose] public section

namespace FreezingGrowth

/-- The longer tree has two initial attachments followed by one freeze. -/
def removalLongWord : Word := [true, true, false] ++ List.replicate 13 true

/-- Delete the second initial attachment from `removalLongWord`. -/
def removalShortWord : Word := [true, false] ++ List.replicate 13 true

theorem removalLongWord_admissible : removalLongWord.admissible := by
  intro j hj
  have hj' : j < 16 := by simpa [removalLongWord] using hj
  interval_cases j <;>
    norm_num [removalLongWord, activeCount, Finset.sum_range_succ, Word.toSigns]

theorem removalShortWord_admissible : removalShortWord.admissible := by
  intro j hj
  have hj' : j < 15 := by simpa [removalShortWord] using hj
  interval_cases j <;>
    norm_num [removalShortWord, activeCount, Finset.sum_range_succ, Word.toSigns]

/-- Pure arithmetic bridge; the two exact computation premises must be certified
before this yields the paper's existential result. -/
theorem removal_height_lt_of_statistics
    (hlong : ProfileCompute.statistics (ProfileCompute.run removalLongWord) =
      (523069747200, 2493235880606))
    (hshort : ProfileCompute.statistics (ProfileCompute.run removalShortWord) =
      (12454041600, 59460503672)) :
    removalLongWord.expectedHeight < removalShortWord.expectedHeight := by
  rw [ProfileCompute.expectedHeight_eq_of_statistics _ _ _ hlong,
    ProfileCompute.expectedHeight_eq_of_statistics _ _ _ hshort]
  norm_num

end FreezingGrowth
