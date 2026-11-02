module

public import FreezingGrowth.HighPopulationReduction
public import FreezingGrowth.ReverseFirstPairDeletion
public import FreezingGrowth.HeightExpectationOrder

/-!
# The corrected high-population reduction, unconditionally

`high_population_domination_of_firstPairDeletion` takes Theorem 1.3 as an
explicit premise. Here that premise is discharged by the actual reverse-forest
proof in `ReverseFirstPairDeletion`, so no comparison hypothesis remains.
The index is the corrected `r - 1` (finding SF2), and the statement is a
height domination only; it is not yet the high branch of Theorem 1.2.
-/

@[expose] public section

namespace FreezingGrowth.Word

/-- A path that reaches `r` active vertices dominates, in upper tails, the
actual height of a pure recursive tree with `r - 1` attachments. -/
theorem high_population_domination (xs : Word) (ha : xs.admissible) {r : ℕ}
    (hhigh : ∃ j ≤ xs.length, (r : ℤ) ≤ activeCount xs.toSigns j) :
    HeightLE (List.replicate (r - 1) true) xs :=
  high_population_domination_of_firstPairDeletion firstPairDeletionClaim xs ha hhigh

/-- The same domination at the level of expected heights. -/
theorem high_population_expectedHeight_ge (xs : Word) (ha : xs.admissible) {r : ℕ}
    (hhigh : ∃ j ≤ xs.length, (r : ℤ) ≤ activeCount xs.toSigns j) :
    Word.expectedHeight (List.replicate (r - 1) true) ≤ xs.expectedHeight :=
  (high_population_domination xs ha hhigh).expectedHeight_le

end FreezingGrowth.Word
