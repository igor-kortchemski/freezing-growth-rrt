module

public import FreezingGrowth.FiniteLaw
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Precise targets for the Introduction

The definitions ending in `Claim` are propositions to be proved, not theorems
or assumptions. No proof of an Introduction result is asserted by this module.
All observables below use the actual forward law, including terminal extinction.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory

/-- The common prefix with exactly two active vertices, for positive `m`. -/
def twoActivePrefix (m : ℕ) : Word :=
  List.replicate m true ++ List.replicate (m - 1) false

/-- Proposition 1.1(i), including its consequence for removing only the freeze.
Both inequalities use the same witnesses, as required by the source. -/
def RemoveFreezeAttachClaim : Prop :=
  ∀ A : ℝ, 0 < A → ∃ m n : ℕ,
    let xs : Word := twoActivePrefix m ++ [false, true] ++ List.replicate n true
    let ys : Word := twoActivePrefix m ++ List.replicate n true
    let zs : Word := twoActivePrefix m ++ List.replicate (n + 1) true
    1 ≤ m ∧ xs.admissible ∧ ys.admissible ∧ zs.admissible ∧
      xs.expectedHeight + A ≤ ys.expectedHeight ∧
      xs.expectedHeight + A ≤ zs.expectedHeight

/-- Proposition 1.1(ii). -/
def RemoveAttachFreezeClaim : Prop :=
  ∀ A : ℝ, 0 < A → ∃ m n : ℕ,
    let xs : Word := twoActivePrefix m ++ [true, false] ++ List.replicate n true
    let ys : Word := twoActivePrefix m ++ List.replicate n true
    1 ≤ m ∧ xs.admissible ∧ ys.admissible ∧ xs.expectedHeight + A ≤ ys.expectedHeight

/-- Proposition 1.1(iii). An exact finite witness would suffice for this
existential claim, but would not prove the later eventual-in-`n` assertion. -/
def RemoveAttachClaim : Prop :=
  ∃ n : ℕ,
    let xs : Word := [true, true, false] ++ List.replicate n true
    let ys : Word := [true, false] ++ List.replicate n true
    xs.admissible ∧ ys.admissible ∧ xs.expectedHeight < ys.expectedHeight

/-- The real threshold in Theorem 1.2, totalized at small `n` by Mathlib's log. -/
noncomputable def mainThreshold (n : ℕ) : ℝ :=
  Real.exp 1 * Real.log n - 5 * Real.log (Real.log n)

/-- Theorem 1.2's uniform probability conclusion. Since each `𝕏ₙ` is finite
and nonempty, this is the epsilon form of its minimum tending to one. -/
def UniformHeightProbabilityClaim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ xs : Word, Word.InFamily n xs →
      1 - ε ≤ xs.heightLaw.real {h : ℕ | mainThreshold n ≤ (h : ℝ)}

/-- Theorem 1.2's expectation conclusion, with a threshold uniform in the word. -/
def UniformHeightExpectationClaim : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ xs : Word, Word.InFamily n xs →
    mainThreshold n ≤ xs.expectedHeight

/-- Theorem 1.3: delete the last attachment of the first positive run and the
first freeze. Validity of the shorter word is a conclusion, not an extra premise. -/
def FirstPairDeletionClaim : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ tail : Word,
    let xs : Word := List.replicate k true ++ [false] ++ tail
    let ys : Word := List.replicate (k - 1) true ++ tail
    xs.admissible → ys.admissible ∧ Word.HeightLE ys xs

end FreezingGrowth
