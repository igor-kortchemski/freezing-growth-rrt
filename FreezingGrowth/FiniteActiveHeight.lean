module

public import FreezingGrowth.FiniteLowProfile
public import FreezingGrowth.ActiveHeightBernoulli

/-! An endpoint-complete form of the Bernoulli representation in the low case. -/

@[expose] public section

namespace FreezingGrowth.Word

open ProbabilityTheory
open scoped BigOperators

/-- Every admissible word has a surviving prefix with the same attachment
count and maximum-height law. On that prefix, the uniform active depth has the
explicit independent-Bernoulli representation. This includes terminal extinction
without assigning a uniform active vertex to an empty set. -/
theorem exists_surviving_bernoulli_representation (xs : Word) (ha : xs.admissible) :
    ∃ k ≤ xs.length, ∃ hk : PositiveThrough xs.toSigns k,
      plusCount xs.toSigns k = xs.attachments ∧
      Forward.heightLaw xs.toSigns k = xs.heightLaw ∧
      HasLaw (fun ω : Fin k → ℕ =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => xs.toSigns (i.val + 1) = true), ω i)
        (Forward.uniformActiveHeightLaw xs.toSigns k)
        (bernoulliProductLaw (populationBernoulliParameter xs.toSigns k hk)) := by
  obtain ⟨k, hkle, hk, hcount, hlaw⟩ := exists_surviving_prefix xs ha
  exact ⟨k, hkle, hk, hcount, hlaw,
    Forward.uniformActiveHeightLaw_sum_hasLaw xs.toSigns k hk⟩

end FreezingGrowth.Word
