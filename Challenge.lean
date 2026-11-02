module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Numbered Introduction main results of arXiv:2505.16571v2

This Challenge has exactly five deliberate theorem placeholders, explicitly
authorized by the user on 2 November 2026 for statement comparison only.
Every model and claim definition is copied from the proved library. No proof
module imports this Challenge; Solution imports the actual proved exports.

`true` means attachment; `false` means freezing. Persistent vertex identifiers,
whole finite forward laws, and the terminal-extinction boundary are retained.
-/

@[expose] public section
namespace FreezingGrowth

/-- Positive-step attachment/freezing schedule; index zero is ignored. -/
abbrev SignSequence := ℕ → Bool


/-- Number of attachments among the first n scheduled operations. -/
def plusCount (x : SignSequence) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if x (i + 1) then 1 else 0

/-- Unstopped integer population walk starting at one. -/
def activeCount (x : SignSequence) (n : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range n, if x (i + 1) then 1 else -1

namespace Forward

/-- Complete labelled tree State, including active vertices, parents and freeze times. -/
structure State where
  vertices : Finset ℕ
  active : Finset ℕ
  graph : SimpleGraph ℕ
  parent : ℕ → ℕ
  height : ℕ → ℕ
  frozenAt : ℕ → Option ℕ

/-- The rooted singleton tree with active root zero. -/
def initial : State where
  vertices := {0}
  active := {0}
  graph := ⊥
  parent := fun _ => 0
  height := fun _ => 0
  frozenAt := fun _ => none

/-- Attach the fresh vertex `t` to the chosen active vertex `v`. -/
def attach (s : State) (t v : ℕ) : State where
  vertices := insert t s.vertices
  active := insert t s.active
  graph := s.graph ⊔ SimpleGraph.edge v t
  parent := Function.update s.parent t v
  height := Function.update s.height t (s.height v + 1)
  frozenAt := Function.update s.frozenAt t none

/-- Freeze the chosen vertex and record its displayed label. -/
def freeze (s : State) (t v : ℕ) : State where
  vertices := s.vertices
  active := s.active.erase v
  graph := s.graph
  parent := s.parent
  height := s.height
  frozenAt := Function.update s.frozenAt v (some t)

/-- Algorithm 1's transition. Invalid choices leave the state unchanged;
all theorems about the process require a legal active choice when one exists. -/
def step (s : State) (t : ℕ) (sign : Bool) (v : ℕ) : State :=
  if v ∈ s.active then if sign then attach s t v else freeze s t v else s

end Forward

namespace Forward

open MeasureTheory
open scoped ENNReal Classical

instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩

/-- Uniform choice of an active vertex; extinction is absorbing. -/
noncomputable def transitionLaw (s : State) (t : ℕ) (sign : Bool) : Measure State :=
  if s.active.Nonempty then
    (Measure.uniformOfFinset s.active).map (fun v => step s t sign v)
  else Measure.dirac s

/-- Actual finite Algorithm 1 tree law, iterated with fresh uniform choices. -/
noncomputable def treeLaw (x : SignSequence) : ℕ → Measure State
  | 0 => Measure.dirac initial
  | n + 1 => (treeLaw x n).bind (fun s => transitionLaw s (n + 1) (x (n + 1)))

end Forward

namespace Forward

open MeasureTheory
open scoped ENNReal Classical

/-- Maximum root distance, using the recursively maintained vertex heights. -/
def treeHeight (s : State) : ℕ := s.vertices.sup s.height

/-- Height pushforward of the complete finite forward-tree law. -/
noncomputable def heightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).map treeHeight

end Forward

/-- Finite Boolean operation word. -/
abbrev Word := List Bool

namespace Word

open MeasureTheory

/-- Extend a finite word to the positive-index convention of `SignSequence`.
The value at zero is unused; indices beyond the word are set to freezing. -/
def toSigns (xs : Word) (i : ℕ) : Bool := xs[i - 1]?.getD false

/-- Every operation has at least one active vertex to choose from. -/
def admissible (xs : Word) : Prop :=
  ∀ j < xs.length, 0 < activeCount (toSigns xs) j

/-- The number of attachment operations, hence the number of tree edges. -/
def attachments (xs : Word) : ℕ := plusCount (toSigns xs) xs.length

/-- The Introduction's family `𝕏ₙ`, including terminal extinction. -/
def InFamily (n : ℕ) (xs : Word) : Prop := admissible xs ∧ attachments xs = n

/-- Height law after all operations in the finite word. -/
noncomputable def heightLaw (xs : Word) : Measure ℕ :=
  Forward.heightLaw xs.toSigns xs.length

/-- Expected actual tree height, as a Bochner integral against its law. -/
noncomputable def expectedHeight (xs : Word) : ℝ :=
  ∫ h : ℕ, (h : ℝ) ∂xs.heightLaw

/-- Stochastic domination through every natural-height upper tail. -/
def HeightLE (xs ys : Word) : Prop :=
  ∀ h : ℕ, xs.heightLaw {k | h ≤ k} ≤ ys.heightLaw {k | h ≤ k}

end Word

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

namespace Paper

theorem theorem_1_2 : UniformHeightProbabilityClaim ∧ UniformHeightExpectationClaim := by
  sorry

theorem theorem_1_3 : FirstPairDeletionClaim := by
  sorry

theorem proposition_1_1_i : RemoveFreezeAttachClaim := by
  sorry

theorem proposition_1_1_ii : RemoveAttachFreezeClaim := by
  sorry

theorem proposition_1_1_iii : RemoveAttachClaim := by
  sorry

end Paper
end FreezingGrowth
